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

/* A best-fit allocator for memory ranges aligned to a big power of 2. */

typedef struct {
  /* size of pages managed, typically Huge_page_log or Page_log */
  int const page_log;
  /* address of each allocated block and its size */
  struct skiplist free_per_address_sk;
  /* each allocated block ordered per decreasing size.

     key: lexicographic ordering by size (decreasing) and address.

       ~( # huge pages )      msbs of address
     |-------------------|------------------------|
        num_max_log bits   small_address_log bits
  */
  struct skiplist free_per_size_sk;
} page_allocator;

#define PA_STATIC_INITIALIZER(page_log) \
  { page_log, SKIPLIST_STATIC_INITIALIZER, SKIPLIST_STATIC_INITIALIZER }

/* Allocate a block of size [request] out of the free blocks of [pa].
   [request] is rounded up to the size of pages managed by [pa].
   Returns 1 on success, 0 if out of free space. */
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
