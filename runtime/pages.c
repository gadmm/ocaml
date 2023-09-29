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
#include "caml/address_class.h"
#include "caml/pages.h"
#include "caml/page_allocator.h"
#include "caml/platform.h"
#include "caml/skiplist.h"

uintnat caml_use_huge_pages = 0;
/* True iff the program wants to allocate heap chunks by mmapping huge
   pages. This is set when parsing [OCAMLRUNPARAM] and must stay
   constant after that.
*/


/* Reserving, committing, decommitting. Platform-independent. */

int caml_mem_reserve(asize_t request, int kind,
                     char **out_block, asize_t *out_reserved)
{
  char *mem;
  request = Round_up(request, Pagetable_entry_size);
  mem = caml_mem_reserve_os(request, Pagetable_entry_size);
  if (mem == NULL) return -1;
  *out_block = mem;
  *out_reserved = request;
  /* keep reserved in case of error of the page table */
  return caml_page_table_add(kind, mem, mem + request);
}

int caml_mem_commit(char *block, asize_t request)
{
  CAMLassert_aligned(block, Real_page_size);
  CAMLassert_aligned(request, Real_page_size);
  /* Commit [block..block+size[ */
  if (-1 == caml_mem_commit_os(block, request)) goto err;
  return 0;
err:
  caml_mem_decommit_os(block, request);
  return -1;
}

void caml_mem_decommit(char * block, asize_t size)
{
  CAMLassert_aligned(block, Real_page_size);
  CAMLassert_aligned(size, Real_page_size);
  caml_mem_decommit_os(block, size);
}

/* VAS allocator for the major heap */

static page_allocator heap_allocator = PA_STATIC_INITIALIZER(Huge_page_log);

int caml_heap_commit(asize_t request, char **out_block, asize_t *out_size)
{
  char *block;
  asize_t obtained;
  if (!caml_pa_alloc(&heap_allocator, request, &block, &obtained)) {
    /* Out of already-reserved space, reserve a large-enough space */
    char *mem;
    asize_t reserved;
    /* We add a padding before and after to prevent coalescing of
       distinct reservations (VirtualAlloc/VirtualFree semantics). */
    asize_t padding = MMAP_COALESCES_RESERVATIONS ? 0 : Huge_page_size;
    asize_t new_request = request + 2 * padding;
    if (-1 == caml_mem_reserve(new_request, In_heap, &mem, &reserved))
      return -1;
    CAMLassert_aligned(mem, Huge_page_size);
    CAMLassert_aligned(reserved, Huge_page_size);
    CAMLassert_aligned(padding, Huge_page_size);
    caml_pa_merge(&heap_allocator, mem + padding, reserved - 2 * padding);
    /* Now it should succeed */
    if (!caml_pa_alloc(&heap_allocator, request, &block, &obtained))
      CAMLassert(0);
  }
  CAMLassert(block != NULL && obtained >= request);
  CAMLassert_aligned(block, Huge_page_size);
  CAMLassert_aligned(obtained, Huge_page_size);
  if (-1 == caml_mem_commit(block, obtained)) goto err;
  *out_block = block;
  *out_size = obtained;
  return 0;
err:
  caml_pa_merge(&heap_allocator, block, obtained);
  return -1;
}

void caml_heap_decommit(char * block, asize_t size)
{
  CAMLassert_aligned(block, Huge_page_size);
  CAMLassert_aligned(size, Huge_page_size);
  caml_mem_decommit(block, size);
  caml_pa_merge(&heap_allocator, block, size);
}
