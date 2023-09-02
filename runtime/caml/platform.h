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

/* Platform-specific constants and common abstraction to OS memory
   allocation */

#ifndef CAML_PLATFORM_H
#define CAML_PLATFORM_H

#ifdef CAML_INTERNALS

#ifndef CAML_NAME_SPACE
#include "compatibility.h"
#endif

#include "config.h"
#include "mlvalues.h"

#include <stdbool.h>

extern uintnat caml_use_huge_pages;

// Real page size can be greater than the Page_size constant
CAMLextern uintnat caml_real_page_size;
#define Real_page_size \
  (CAMLassert(caml_real_page_size != 0), caml_real_page_size)

#ifdef ARCH_SIXTYFOUR
/* Number of significant bits of pointers on this platform. Affects
   PA_num_max_log. Can easily support e.g. 57 bits at some point. */
#ifdef __aarch64__
#define Significant_ptr_bits 49 // 48 + TTB selection
#else
#define Significant_ptr_bits 48
#endif
#else
#define Significant_ptr_bits 32
#endif /* ARCH_SIXTYFOUR */

/* There does not seem to be a way to ask the OS for the size of a
   huge page. Some systems have them different from 2MB.
   According to sources:
     x86-64 -> 2MB
     arm -> 2MB (& 4KB) or 512MB (& 64 KB)
     ppc64 -> 16MB
*/
#ifdef __powerpc64__
#define Huge_page_log 24 // 16MB
#else
#define Huge_page_log 21 // 2MB
#endif

#define Huge_page_size ((uintnat)1 << Huge_page_log)

/* On Linux, mmap grows downwards. This is used heuristically only. */
#ifdef __linux__
#define MMAP_GROWS_DOWN 1
#else
#define MMAP_GROWS_DOWN 0
#endif

/* On Linux with overcommitting, prefault pages to avoid SIGBUS in
   out-of-memory situations? This is slow. (Note: the program
   still stops if the allocation failure happens during minor
   collection.) */
#define DO_POPULATE 0

/* On Windows, reservations do not coalesce; one must be careful not
   to cross reservation boundaries with [caml_mem_commit_os] and
   [caml_mem_decommit_os]. */
#ifdef _WIN32
#define MMAP_COALESCES_RESERVATIONS 0
#else
#define MMAP_COALESCES_RESERVATIONS 1
#endif

char *caml_mem_reserve_os(asize_t size, asize_t align);
bool caml_mem_commit_os(char *block, asize_t size);
void caml_mem_decommit_os(char * block, asize_t size);

void caml_mem_os_init(void);
void caml_mem_unreserve_all(void);

#endif /* CAML_INTERNALS */
#endif /* CAML_PLATFORM_H */
