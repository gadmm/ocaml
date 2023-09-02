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
#include <stdatomic.h>
#include <unistd.h>
#include <sys/mman.h>
#include "caml/address_class.h"
#include "caml/pages.h"
#include "caml/page_allocator.h"
#include "caml/platform.h"
#include "caml/skiplist.h"

uintnat caml_use_huge_pages = 1;
/* True iff the program wants to allocate heap chunks by mmapping huge
   pages. This is set when parsing [OCAMLRUNPARAM] and must stay
   constant after that.
*/

/* Reserving, committing, decommitting. Platform-independent. */


/* Round up to the nearest small page or huge page, depending on what
   is best. */
static asize_t round_up_to_huge_page(asize_t size)
{
  asize_t page_size = caml_use_huge_pages ? Huge_page_size : Real_page_size;
  return round_up(size, page_size);
}

// reserve at least [request] contiguous memory, rounded up to the
// Pagetable_entry_size and record it with the page table.
int caml_mem_reserve(asize_t request, int kind,
                     char **out_block, asize_t *out_reserved)
{
  char *mem;
  request = round_up(request, Pagetable_entry_size);
  mem = caml_mem_reserve_os(request, Pagetable_entry_size);
  if (mem == NULL) return -1;
  *out_block = mem;
  *out_reserved = request;
  /* keep reserved in case of error of the page table */
  return caml_page_table_add(kind, mem, mem + request);
}

/* [block] must be aligned to huge pages, and there must be enough
   reserved space to round the request up to the nearest page or huge
   page. If successful, [out_size] is set to the size that was
   actually committed. In case of error the whole range is
   now invalid. */
int caml_mem_commit(char *block, asize_t request, asize_t *out_size)
{
  request = round_up_to_huge_page(request);
  /* Commit [block..block+size[ */
  if (-1 == caml_mem_commit_os(block, request)) goto err;
  *out_size = request;
  return 0;
err:
  caml_mem_decommit_os(block, request);
  return -1;
}

/* [block] and [size] must be aligned to Real_page_size. */
void caml_mem_decommit(char * block, asize_t size)
{
  caml_mem_decommit_os(block, size);
}

/* VAS allocator for the major heap */

static page_allocator heap_allocator = PA_STATIC_INITIALIZER(Huge_page_log);

int caml_heap_commit(asize_t request, char **out_block,
                     asize_t *out_size, asize_t *out_reserved)
{
  char *block;
  asize_t reserved;
  if (!caml_pa_alloc(&heap_allocator, request, &block, &reserved)) {
    // Out of already-reserved space
    char *mem;
    asize_t new_reserve;
    // Reserve a large-enough space
    if (-1 == caml_mem_reserve(request, In_heap, &mem, &new_reserve))
      return -1;
    caml_pa_merge(&heap_allocator, mem, new_reserve);
    // Now it should succeed
    caml_pa_alloc(&heap_allocator, request, &block, &reserved) ?: CAMLassert(0);
  }
  if (-1 == caml_mem_commit(block, request, &request)) goto err;
  *out_block = block;
  *out_size = request;
  *out_reserved = reserved;
  return 0;
err:
  caml_pa_merge(&heap_allocator, block, reserved);
  return -1;
}

void caml_heap_decommit(char * block, asize_t size)
{
  caml_mem_decommit(block, size);
  caml_pa_merge(&heap_allocator, block, size);
}
