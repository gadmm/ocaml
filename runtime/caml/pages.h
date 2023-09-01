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
#include "gc.h"

#ifdef __cplusplus
extern "C" {
#endif

extern uintnat caml_use_huge_pages;

// Mask for the hardcoded page size (fast), used for static data
#define Page_mask (~(Page_size - 1))

// Real page size can be greater. (slower than the constant)
CAMLextern uintnat caml_real_page_size;
#define Real_page_size \
  (CAMLassert(caml_real_page_size != 0), caml_real_page_size)

/* There does not seem to be a way to ask the OS for the size of a
   huge page. Legends tell that some systems have them larger than
   2MB. Let's try:
     x86-64, arm -> 2MB
     i386 -> 4MB
     ppc64 -> 64MB
*/
#define Huge_page_log 21 // 2MB
#define Huge_page_size ((uintnat)1 << Huge_page_log)

static_assert(Huge_page_log <= Pagetable_entry_log, "invalid page sizes");
static_assert(Page_log < Huge_page_log, "invalid page sizes");

asize_t caml_round_up_to_huge_page(asize_t size);
int caml_mem_reserve(asize_t request, int kind,
                     char **out_block, asize_t *out_reserved);
int caml_mem_commit(char *block, asize_t request, asize_t *out_size);
void caml_mem_decommit(char * block, asize_t size);
int caml_mem_commit_os(char *block, asize_t size);
void caml_mem_decommit_os(char * block, asize_t size);

int caml_heap_commit(asize_t request, char **out_block,
                     asize_t *out_size, asize_t *out_reserved);
void caml_heap_decommit(char * block, asize_t size);

#define CAMLassert_aligned_(n, m)                     \
  (CAMLassert(((uintnat)n & ((uintnat)m - 1)) == 0))
#define CAMLassert_aligned(n, m)                          \
  (CAMLassert_is_power_of_2(m),CAMLassert_aligned_(n,m))
#define CAMLassert_is_power_of_2(n) CAMLassert_aligned_(n, n)

Caml_inline intnat round_down(intnat n, intnat mod)
{
  return mod * (n / mod  - (n < 0 ? 1 : 0));
}

Caml_inline intnat round_up(intnat n, intnat mod)
{
  return round_down(n + mod - 1, mod);
}

#ifdef __cplusplus
}
#endif

#endif /* CAML_INTERNALS */
#endif /* CAML_PAGES_H */
