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

#ifndef CAML_PAGES_H
#define CAML_PAGES_H

#ifdef CAML_INTERNALS

#ifndef CAML_NAME_SPACE
#include "compatibility.h"
#endif

#include "config.h"
#include "mlvalues.h"

#ifdef __cplusplus
extern "C" {
#endif

extern uintnat caml_use_huge_pages;

/* reserve at least [request] contiguous memory, rounded up to the
   Pagetable_entry_size and record it with the page table. */
int caml_mem_reserve(asize_t request, int kind,
                     char **out_block, asize_t *out_reserved);

/* [block] and [request] must be aligned to the real page size. In
   case of error the whole range is now invalid. It recognizes blocks
   and sizes that are aligned to huge pages. */
int caml_mem_commit(char *block, asize_t request);

/* [block] and [size] must be aligned to Real_page_size. Whether one
   can decommit accross several distinct reservations (output of
   caml_mem_reserve) is determined by MMAP_COALESCES_RESERVATIONS from
   platform.h. */
void caml_mem_decommit(char * block, asize_t size);

/* Allocation and deallocation for the major heap. */
int caml_heap_commit(asize_t request, char **out_block, asize_t *out_size);
void caml_heap_decommit(char * block, asize_t size);

#ifdef __cplusplus
}
#endif

#endif /* CAML_INTERNALS */
#endif /* CAML_PAGES_H */
