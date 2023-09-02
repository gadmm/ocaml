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
#include <unistd.h>
#include <sys/mman.h>
#include "caml/address_class.h"
#include "caml/pages.h"
#include "caml/platform.h"

/* Page table management */

atomic_char *caml_heap_table = NULL;

#ifdef ARCH_SIXTYFOUR

#ifndef NO_NAKED_POINTER
/* Determines area committed up-front for the page table. Should
   remains at most 48 bits even on 57-bit address spaces as this is
   all that is needed for backwards-compatibility (similarly we could
   omit the kernel space, but we do not).

   (This represents approx 4 MB mapped initially to the zero page.
   This does not consume physical memory, and on overcommitting
   systems does not count towards a memory limit.)

   Can be set to zero if we require that page_table_commit or
   caml_page_table_add is required to announce out-of-heap areas
   beforehand. */
#define Pagetable_initial_bits 48
#else
/* Commit the page table on demand; no need to support unannounced naked
   pointers. */
#define Pagetable_initial_bits 0
#endif

#else

#define Pagetable_initial_bits 32

#endif /* ARCH_SIXTYFOUR */

#define Pagetable_log (Pagetable_significant_bits - Pagetable_entry_log)
#define Pagetable_size (((int)1 << Pagetable_log))
#define Pagetable_initial_size                                  \
  (((int)1 << (Pagetable_initial_bits - Pagetable_entry_log)))

static_assert(Pagetable_log < 8 * sizeof(int), "invalid page sizes");
static_assert(Huge_page_log <= Pagetable_entry_log, "invalid page sizes");

void caml_page_table_release(void)
{
  int ret = 0;
  CAMLassert(caml_heap_table != NULL);
  ret = munmap(caml_heap_table - (Pagetable_size / 2), Pagetable_size);
  CAMLassert(ret != -1 || errno != EINVAL);
  (void)ret;
}

int caml_page_table_initialize(mlsize_t bytesize)
{
  int ret = 0;
  // TODO: win32
  void *block = mmap(NULL, Pagetable_size, PROT_NONE,
                     MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  if (block == MAP_FAILED) return -1;
  /* Kernel addresses are represented with negative offsets */
  caml_heap_table = (atomic_char *)block + (Pagetable_size / 2);
  caml_real_page_size = sysconf(_SC_PAGESIZE);
  CAMLassert(caml_real_page_size >= Page_size);
  /* Commit initial portion */
  ret = mprotect(caml_heap_table - (Pagetable_initial_size / 2),
                 Pagetable_initial_size, PROT_READ | PROT_WRITE);
  CAMLassert(ret != -1 || errno == ENOMEM);
  if (ret == -1) goto err;
  return 0;
 err:
  caml_page_table_release();
  return -1;
}

/* This is called infrequently, and for a small portion of
   caml_heap_table, thanks to the hints given to mmap inside
   [caml_alloc_for_heap] which tends to reserve heap inside
   already-committed pages of caml_heap_table. */
static int page_table_commit(intnat start, intnat end)
{
  int ret = 0;
  intnat page_start = round_down(start, Real_page_size);
  intnat page_end = round_up(end, Real_page_size);
  uintnat size = page_end - page_start;
  if (page_start >= -(Pagetable_initial_size / 2)
      && page_end <= Pagetable_initial_size / 2) {
    /* Part of the initial portion already committed, avoid a
       syscall. */
    return 0;
  }
  CAMLassert(page_start >= -(Pagetable_size / 2));
  CAMLassert(page_end <= Pagetable_size / 2);
  ret = mprotect(&caml_heap_table[page_start], size, PROT_READ | PROT_WRITE);
  CAMLassert(ret != -1 || errno == ENOMEM);
  return ret;
}

// Assumes that the caller owns the mapping from start to end, to
// ensure that we are not racing to set the same entry twice.
// Idempotent (returns 0 even if some page table entries are already
// set to [kind]).
int caml_page_table_add(int kind, void * start, void * end)
{
  int pstart = Pagetable_entry(start);
  int pend = Pagetable_entry((intnat)end - 1) + 1;
  int p;
  int ret = 0;
  if (-1 == page_table_commit(pstart, pend)) return -1;
  for (p = pstart; p < pend; p++) {
    char e = 0;
    if (!atomic_compare_exchange_strong_explicit(&caml_heap_table[p], &e,
                                                 kind, memory_order_acq_rel,
                                                 memory_order_acquire))
      // It is currently a programming error to:
      // - Let foreign pointers be seen by the OCaml GC
      // - Release the underlying mapping of these pointers, so that
      //   the same virtual space can later be acquired by the OCaml
      //   runtime.
      //
      // However we could relax these conditions for libraries that
      // are ready to declare their pages in advance, in that case
      // they can free their mapping and we just find someplace else.
      // To implement this we just need a third error value and adjust
      // the callers.
      //
      // This ensures that the heap table is monotonic. This does not
      // ensure safety (there is no guarantee that the GC has the time
      // to see all the naked pointers before OCaml acquires the
      // mapping, except in situations where the outside world
      // declared their pages of interest in advances).
      if (e != kind) ret = -1;
  }
  return ret;
}
