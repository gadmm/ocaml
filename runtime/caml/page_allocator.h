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

/* Allocation macros and functions */

#ifndef CAML_PAGE_ALLOCATOR_H
#define CAML_PAGE_ALLOCATOR_H

/* This is a best-fit allocator for memory ranges aligned to a power
   of 2 ("pages"). It depends on a parameter [page_log] which is the
   log_2 of the granularity and alignment of the allocations.

   It can serve requests up to a size of 2^N where:
    - N = 16+2*page_log on x86-64
      (page_log=Page_log: 1TB, page_log=Heap_page_log: 1PB)
    - N = 15+2*page_log on arm64
      (page_log=Page_log: 512GB, page_log=Heap_page_log: 512TB)
    - N = 2*page_log on x86 (32-bit)
      (page_log=Page_log: 16MB, page_log=Heap_page_log: 16GB)

   It is possible to have a [page_log] much smaller than Page_log if
   one has a natural way to deal with requests that are too big (e.g.
   when large allocations can be treated differently from small
   allocations).
 */

#ifdef CAML_INTERNALS

#ifndef CAML_NAME_SPACE
#include "compatibility.h"
#endif

#include "config.h"
#include "mlvalues.h"
#include "skiplist.h"

#ifdef __cplusplus
extern "C" {
#endif

typedef struct {
  /* size of pages managed, typically Huge_page_log or Page_log */
  int const page_log;
  /* address of each allocated block and its size */
  struct skiplist free_per_address_sk;
  /* each allocated block ordered per decreasing size.

     key: lexicographic ordering by size (decreasing) and address.

          ~( # pages )            msbs of address
     |---------------------|---------------------------|
       PA_num_max_log bits   PA_small_address_log bits
  */
  struct skiplist free_per_size_sk;
} page_allocator;

#define PA_STATIC_INITIALIZER(page_log) \
  { page_log, SKIPLIST_STATIC_INITIALIZER, SKIPLIST_STATIC_INITIALIZER }

/* Allocate a block of size [request] out of the free blocks of [pa].
   [request] is rounded up to the size of pages managed by [pa]. The
   result of the allocation is stored in [block_out]. [size_out] can
   be NULL, if not, it receives the actual allocated size. Returns 1
   on success, 0 if out of free space or if the request is too large. */
int caml_pa_alloc(page_allocator *pa, asize_t request,
                  char **block_out, asize_t *size_out);

/* Add a range ([block],[block]+[size]) to [pa], with coalescing. The
   range must not overlap with existing ranges in the allocator. */
void caml_pa_merge(page_allocator *pa, char *block, asize_t size);

/* Find in [pa] the block with greatest address lower or equal to
   [addr]. Return 1 if found, 0 if not found. */
int caml_pa_find_below_address(page_allocator *pa, char *addr,
                               char **block_out, asize_t *size_out);

/* Print [pa] to stderr. */
void caml_pa_print(page_allocator *pa);

#ifdef __cplusplus
}
#endif

#endif /* CAML_INTERNALS */
#endif /* CAML_PAGE_ALLOCATOR_H */
