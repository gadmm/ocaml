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

#ifndef CAML_PLATFORM_H
#define CAML_PLATFORM_H

#ifdef CAML_INTERNALS

#ifndef CAML_NAME_SPACE
#include "compatibility.h"
#endif

#include "config.h"
#include "mlvalues.h"

#ifdef __cplusplus
extern "C" {
#endif

// Real page size can be greater than the Page_size constant
CAMLextern uintnat caml_real_page_size;
#define Real_page_size \
  (CAMLassert(caml_real_page_size != 0), caml_real_page_size)

/* There does not seem to be a way to ask the OS for the size of a
   huge page. Some systems have them different from 2MB.
   According to sources:
     x86-64, arm -> 2MB
     ppc64 -> 64MB
*/
#define Huge_page_log 21 // 2MB
#define Huge_page_size ((uintnat)1 << Huge_page_log)

/* On Linux, mmap grows downwards. This is used heuristically only. */
#ifdef __linux__
#define MMAP_GROWS_DOWN 1
#else
#define MMAP_GROWS_DOWN 0
#endif

/* On Windows, reservations do not coalesce; one must be careful not
   to cross reservation boundaries with [caml_mem_commit_os] and
   [caml_mem_decommit_os]. */
#ifdef _WIN32
#define MMAP_COALESCES_RESERVATIONS 0
#else
#define MMAP_COALESCES_RESERVATIONS 1
#endif

char *caml_mem_reserve_os(asize_t size, asize_t align);
int caml_mem_commit_os(char *block, asize_t size);
void caml_mem_decommit_os(char * block, asize_t size);

void caml_mem_os_init(void);
void caml_mem_unreserve_all(void);

#ifdef __cplusplus
}
#endif

#endif /* CAML_INTERNALS */
#endif /* CAML_PLATFORM_H */
