/**************************************************************************/
/*                                                                        */
/*                                 OCaml                                  */
/*                                                                        */
/*        Guillaume Munch-Maccagnoni, projet Gallinette, INRIA            */
/*                                                                        */
/*   Copyright 2023 Institut National de Recherche en Informatique et     */
/*     en Automatique.                                                    */
/*                                                                        */
/*   All rights reserved.  This file is distributed under the terms of    */
/*   the GNU Lesser General Public License version 2.1, with the          */
/*   special exception on linking described in the file LICENSE.          */
/*                                                                        */
/**************************************************************************/

#define CAML_INTERNALS

#include <assert.h>
#include <errno.h>
#include <stdbool.h>
#include "caml/heap_map.h"
#include "caml/heap_allocator.h"
#include "caml/page_allocator.h"
#include "caml/platform.h"
#include "caml/skiplist.h"

bool caml_mem_reserve(asize_t request, int kind,
                      char **out_block, asize_t *out_reserved)
{
  char *mem;
  request = Round_up(request, Pagetable_entry_size);
  mem = caml_mem_reserve_os(request, Pagetable_entry_size);
  if (mem == NULL) return false;
  *out_block = mem;
  *out_reserved = request;
  /* keep reserved in case of error of the heap table */
  return caml_heap_table_add(kind, mem, mem + request);
}

bool caml_mem_commit(char *block, asize_t request)
{
  CAMLassert_aligned(block, Real_page_size);
  CAMLassert_aligned(request, Real_page_size);
  /* Commit [block..block+size[ */
  if (!caml_mem_commit_os(block, request)) goto err;
  return true;
err:
  caml_mem_decommit_os(block, request);
  return false;
}

void caml_mem_decommit(char * block, asize_t size)
{
  CAMLassert_aligned(block, Real_page_size);
  CAMLassert_aligned(size, Real_page_size);
  caml_mem_decommit_os(block, size);
}

/* VAS allocator for the major heap */

#define Heap_page_log 17 /* 128 KB */
#define Heap_page_size ((uintnat)1 << Heap_page_log)

CAML_STATIC_ASSERT(Pagetable_entry_size >= Huge_page_size);
CAML_STATIC_ASSERT(Huge_page_size >= Heap_page_size);

static page_allocator heap_allocator = PA_STATIC_INITIALIZER(Heap_page_log);
static page_allocator huge_allocator = PA_STATIC_INITIALIZER(Huge_page_log);

bool caml_heap_commit(asize_t request, char **out_block, asize_t *out_size)
{
  char *block;
  asize_t obtained;

  /* Allocate a huge-aligned region if the request is almost huge. If
     [caml_use_huge_pages] is true, or e.g. THP is always enabled,
     this will result in the allocation of huge pages. */
  bool huge = request > Huge_page_size / 2;
  page_allocator *page_allocator = huge ? &huge_allocator : &heap_allocator;
  asize_t page_size = huge ? Huge_page_size : Heap_page_size;

  CAMLassert(Heap_page_size >= Real_page_size);

  if (!caml_pa_alloc(page_allocator, request, &block, &obtained)) {
    /* Out of already-reserved space, reserve a large-enough space */
    char *mem;
    asize_t reserved;
    /* We add a padding before and after to prevent coalescing of
       distinct reservations (VirtualAlloc/VirtualFree semantics). */
    asize_t padding = MMAP_COALESCES_RESERVATIONS ? 0 : page_size;
    asize_t new_request = request + 2 * padding;
    if (!caml_mem_reserve(new_request, In_heap, &mem, &reserved))
      return false;
    CAMLassert_aligned(mem, page_size);
    CAMLassert_aligned(reserved, page_size);
    CAMLassert_aligned(padding, page_size);
    caml_pa_merge(page_allocator, mem + padding, reserved - 2 * padding);
    /* Now it should succeed */
    if (!caml_pa_alloc(page_allocator, request, &block, &obtained)) {
      /* Request too big? (> 512TB on 64bit) */
      CAMLassert(0);
      return false;
    }
  }
  CAMLassert(block != NULL && obtained >= request);
  CAMLassert_aligned(block, page_size);
  CAMLassert_aligned(obtained, page_size);
  if (!caml_mem_commit(block, obtained)) goto err;
  *out_block = block;
  *out_size = obtained;
  return true;
err:
  caml_pa_merge(page_allocator, block, obtained);
  return false;
}

void caml_heap_decommit(char * block, asize_t size)
{
  bool huge =
    Is_aligned(block, Huge_page_size) && Is_aligned(size, Huge_page_size);
  CAMLassert_aligned(block, Heap_page_size);
  CAMLassert_aligned(size, Heap_page_size);
  caml_mem_decommit(block, size);
  caml_pa_merge(huge ? &huge_allocator : &heap_allocator, block, size);
}
