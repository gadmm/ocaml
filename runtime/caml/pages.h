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

int caml_mem_reserve(asize_t request, int kind,
                     char **out_block, asize_t *out_reserved);
int caml_mem_commit(char *block, asize_t request, asize_t *out_size);
void caml_mem_decommit(char * block, asize_t size);

int caml_heap_commit(asize_t request, char **out_block,
                     asize_t *out_size, asize_t *out_reserved);
void caml_heap_decommit(char * block, asize_t size);

#ifdef __cplusplus
}
#endif

#endif /* CAML_INTERNALS */
#endif /* CAML_PAGES_H */
