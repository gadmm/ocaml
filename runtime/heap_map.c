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
#include <string.h>
#include "caml/heap_map.h"
#include "caml/memory.h"
#include "caml/page_allocator.h"
#include "caml/platform.h"

/* Heap map management */

atomic_char *caml_heap_table = NULL;

#ifdef ARCH_SIXTYFOUR
/* Determines the area committed up-front for the heap table. We
   consider initially 48 significant bits (+ TTB selection bit on
   arm). Even if we support 57-bit address spaces later on, this is
   all that is needed for backwards-compatibility since the rest can
   be committed on-demand, and one has to go an extra mile to allocate
   foreign pointers outside of the 48-bit range on those systems.
   (With the same reasoning we could exclude the kernel space to
   shrink the initial space in half.)

   This represents 4 MB mapped initially to the zero page. It does not
   consume physical memory apart from the couple of pages that are
   modified later on.

   In a hypothetical model where unannounced foreign pointers are
   forbidden (i.e. not previously announced with heap_table_commit),
   the initial size can be set to zero. However this is a breaking
   change even in "no naked pointers" mode. */
#  ifdef __aarch64__
#    define Pagetable_initial_bits 49
#  else
#    define Pagetable_initial_bits 48
#  endif
#else
#  define Pagetable_initial_bits 32
#endif /* ARCH_SIXTYFOUR */

#define Pagetable_log (Significant_ptr_bits - Pagetable_entry_log)
#define Pagetable_size (((int)1 << Pagetable_log))
#define Pagetable_initial_size                                  \
  (((int)1 << (Pagetable_initial_bits - Pagetable_entry_log)))

/* gcc 4.8 & MSVC compat */
#ifndef static_assert
#ifdef _WIN32
#include <crtdbg.h>
#define static_assert(a, b) _STATIC_ASSERT((a))
#else
#define static_assert _Static_assert
#endif
#endif /* !defined(static_assert) */

static_assert(Pagetable_log < 8 * sizeof(int) - 1, "invalid page sizes");
static_assert(Huge_page_log <= Pagetable_entry_log, "invalid page sizes");

bool caml_heap_table_initialize(mlsize_t bytesize)
{
#ifdef ARCH_SIXTYFOUR
  bool success = 0;
  void *block = caml_mem_reserve_os(Pagetable_size, Page_size);
#else
  /* On 32-bit, the table is smaller than a page */
  void *block = caml_stat_calloc_noexc(Pagetable_size, 1);
#endif
  if (block == NULL) goto err;
  /* Kernel addresses are represented with negative offsets */
  caml_heap_table = (atomic_char *)block + (Pagetable_size / 2);
#ifdef ARCH_SIXTYFOUR
  /* Commit initial portion */
  success =
    caml_mem_commit_os((char *)caml_heap_table - (Pagetable_initial_size/2),
                       Pagetable_initial_size);
  CAMLassert(success || errno == ENOMEM);
  if (!success) goto err;
#endif
  return success;
 err:
  caml_gc_message(0x1000,
                  "heap table allocation failed "
                  "(reserving %u bytes, committing %u bytes), "
                  "strerror()=%s\n",
                  Pagetable_size, Pagetable_initial_size, strerror(errno));
  return success;
}

/* This is called infrequently, and for a small portion of
   caml_heap_table, thanks to the hints given to mmap inside
   [caml_alloc_for_heap] which tends to reserve heap inside
   already-committed pages of caml_heap_table. */
static bool heap_table_commit(int start, int end)
{
  bool success = 0;
#ifdef ARCH_SIXTYFOUR
  int page_start = Round_down(start, Real_page_size);
  int page_end = Round_up(end, Real_page_size);
  intnat size = (intnat)page_end - (intnat)page_start;
  CAMLassert(start < end);
  if (page_start >= -(Pagetable_initial_size / 2)
      && page_end <= Pagetable_initial_size / 2) {
    /* Part of the initial portion which is already committed, avoid a
       syscall. */
    return true;
  }
  CAMLassert(page_start >= -(Pagetable_size / 2));
  CAMLassert(page_end <= Pagetable_size / 2);
  success = caml_mem_commit_os((char *)&caml_heap_table[page_start], size);
  CAMLassert(success || errno == ENOMEM);
  if (!success) {
    caml_gc_message(0x1000,
                    "failed to commit heap table "
                    "(start=%d, end=%d), strerror()=%s\n",
                    start, end, strerror(errno));
  }
#endif
  return success;
}

// Assumes that the caller owns the mapping from start to end, so we
// know that we are not racing to set the same entry twice.
// Idempotent (returns true even if some heap table entries are already
// set to [kind]). Returns false on error.
bool caml_heap_table_add(int kind, void *start, void *end)
{
  int pstart = Pagetable_entry(start);
  int pend = Pagetable_entry((intnat)end - 1) + 1;
  int p;
  bool success = true;
  if (end < start) return false;
  if (!heap_table_commit(pstart, pend)) return false;
  for (p = pstart; p < pend; p++) {
    char e = 0;
#ifdef HAS_ATOMICS
    if (!atomic_compare_exchange_strong_explicit(&caml_heap_table[p], &e,
                                                 kind, memory_order_acq_rel,
                                                 memory_order_acquire)) {
#else
    if (e = caml_heap_table[p], e == 0) {
      caml_heap_table[p] = kind;
    } else {
#endif
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
      if (e != kind) {
        caml_gc_message(0x1000,
                        "failed to set heap table "
                        "(start=%p, end=%p, pstart=%d, pend=%d, p=%d, "
                        "old_kind=%d, new_kind=%d)\n",
                        start, end, pstart, pend, p, e, kind);
        success = false;
      }
    }
  }
  return success;
}

/* Static data table */

/* The allocation size limit is not a problem on 32-bit since this is
   used for lookup and not allocation. */
static page_allocator static_area = PA_STATIC_INITIALIZER(Page_log);

bool caml_is_in_static_data(void *addr)
{
  char *block;
  asize_t size;
  return caml_pa_find_below_address(&static_area, (char *)addr, &block, &size)
    && (char *)addr < block + size;
}

#define Page_mask (~(Page_size - 1))

void caml_static_area_add(void *start, void *end)
{
  uintnat pstart = (uintnat)start & Page_mask;
  uintnat pend = ((uintnat)end - 1) & Page_mask;
  uintnat addr;
  for (addr = pstart; addr <= pend; addr += Page_size) {
    char *p = (char *)addr;
    if (!caml_is_in_static_data(p))
      caml_pa_merge(&static_area, p, Page_size);
  }
}

bool caml_heap_table_add_static_data(void *start, void *end)
{
  if (!caml_heap_table_add(Unmanaged, start, end))
    return false;
  caml_static_area_add(start, end);
  return true;
}
