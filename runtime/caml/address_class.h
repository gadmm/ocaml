/**************************************************************************/
/*                                                                        */
/*                                 OCaml                                  */
/*                                                                        */
/*              Damien Doligez, projet Para, INRIA Rocquencourt           */
/*                                                                        */
/*   Copyright 1996 Institut National de Recherche en Informatique et     */
/*     en Automatique.                                                    */
/*                                                                        */
/*   All rights reserved.  This file is distributed under the terms of    */
/*   the GNU Lesser General Public License version 2.1, with the          */
/*   special exception on linking described in the file LICENSE.          */
/*                                                                        */
/**************************************************************************/

/* Classification of addresses for GC and runtime purposes. */

/* The current runtime supports two different configurations that
   correspond to two different value models, depending on whether
   "naked pointers", that do not point to a well-formed OCaml block,
   are allowed (considered valid values).

   In "classic mode", naked pointers are allowed, and the
   implementation uses a page table. A valid value is then either:
   - a tagged integer (Is_long or !Is_block from mlvalues.h)
   - a pointer to the minor heap (Is_young)
   - a pointer to the major heap (Is_in_heap)
   - a pointer to a constant block statically-allocated by OCaml code
     or the OCaml runtime (Is_in_static_data)
   - a "foreign" pointer, which is none of the above; the destination
     of those pointers may be a well-formed OCaml blocks, but it may
     also be a naked pointer.

   The macros and functions below give access to a global page table
   to classify addresses to be able to implement Is_in_heap,
   In_static_data (or their disjunction Is_in_value_area) and thus
   detect values which may be naked pointers. The runtime
   conservatively assumes that all foreign pointers may be naked
   pointers, and uses the page table to not dereference/follow them.

   In "no naked pointers" mode (when NO_NAKED_POINTERS is defined),
   naked pointers are illegal, so pointers that are values can always
   be assumed to point to well-formed blocks.

   To support an implementation without a global page table, runtime
   code should not rely on Is_in_heap and Is_in_static_data. This
   corresponds to a simpler model where a valid value is either:
   - a tagged integer (Is_long)
   - a pointer to the minor heap (Is_young)
   - a pointer to a well-formed block outside the minor heap
     (it may be in the major heap, or static, or a foreign pointer,
      without a check to distinguish the various cases).

   (To create a well-formed block outside the heap that the GC will
   not scan, one can use the Caml_out_of_heap_header from mlvalues.h.)
*/

#ifndef CAML_ADDRESS_CLASS_H
#define CAML_ADDRESS_CLASS_H

#include <assert.h>
#include <stdatomic.h>

#include "config.h"
#include "misc.h"
#include "mlvalues.h"

/* Use the following macros to test an address for the different classes
   it might belong to. */

#define Is_young(val) \
  (CAMLassert (Is_block (val)), \
   (char *)(val) < (char *)Caml_state_field(young_alloc_end) && \
   (char *)(val) > (char *)Caml_state_field(young_alloc_start))

#define Is_in_heap(a) (caml_classify_address((void*)a, In_heap))

#ifdef NO_NAKED_POINTERS

#define Is_in_heap_or_young(a) 1
#define Is_in_value_area(a) 1

#else

#define Is_in_heap_or_young(a) \
  (caml_classify_address((void*)a, In_heap | In_young))

#define Is_in_value_area(a) (caml_is_in_value_area((void *)a))

#endif /* NO_NAKED_POINTERS */

/***********************************************************************/
/* The rest of this file is private and may change without notice. */

#define In_heap 1
#define In_young 2
#define Unmanaged 4

// Mask for the hardcoded page size (fast), used for static data
#define Page_mask (~(Page_size - 1))

// Real page size can be greater. (slower)
CAMLextern uintnat caml_real_page_size;
#define Real_page_size \
  (CAMLassert(caml_real_page_size !=0), caml_real_page_size)
#define Real_page_mask (~(Real_page_size - 1))

/* There does not seem to be a way to ask the OS for the size of a
   huge page. Legends tell that some systems have them larger than
   2MB. Let's try:
     x86-64, arm -> 2MB
     i386 -> 4MB
     ppc64 -> 64MB
*/
#define Huge_page_log 21 // 2MB
#define Huge_page_size ((uintnat)1 << Huge_page_log)

/* Page table: bitmap */

#ifdef ARCH_SIXTYFOUR

// it is enough to support only non-kernel addresses for realistic
// usecases
#define PAGETABLE_ALLOW_KERNEL_ADDRESSES 1

// TODO: might be better at 1GB (L4 idx + L3 idx)
#define Pagetable_entry_log 28 // 256MB

#if PAGETABLE_ALLOW_KERNEL_ADDRESSES
// can support 57 bits one day
#define Pagetable_significant_bits 48
#define Pagetable_entry(p)                                            \
  (((uintnat)(p) & (((uintnat)1 << Pagetable_significant_bits) - 1))  \
   >> Pagetable_entry_log)
#else
// one less instruction
#define Pagetable_significant_bits 47
#define Pagetable_entry(p) \
  (CAMLassert(0 == ((uintnat)(p) >> Pagetable_significant_bits)), \
   (uintnat)(p) >> Pagetable_entry_log)
#endif

#else

#define Pagetable_significant_bits 32
#define Pagetable_entry_log (Page_log + 2) // 16KB
#define Pagetable_entry(p) ((uintnat)(p) >> Pagetable_entry_log)

#endif /* ARCH_SIXTYFOUR */

#define Pagetable_entry_size ((uintnat)1 << Pagetable_entry_log)

static_assert(Huge_page_log < Pagetable_entry_log, "invalid page sizes");
static_assert(Page_log < Huge_page_log, "invalid page sizes");

CAMLextern atomic_char *caml_heap_table;

int caml_is_in_static_data(void *a);

inline int caml_classify_address(void *a, int kind)
{
  uintnat p = Pagetable_entry(a);
  char e = atomic_load_explicit(&caml_heap_table[p], memory_order_relaxed);
  CAMLassert(kind != 0);
  if (LIKELY(e != 0)) {
    /* no synchronisation required */
    return e & kind;
  }
  // e == 0
  /* This measures the cost of synchronisation in multicore: the
     current branch occurs infrequently-enough (at most once per
     visited heap table entry per domain, by monotonicity of the page
     table) that the cost of the atomic operation itself would be
     negligible. But we also have to count code layout, branch
     mispredictions, etc. which could affect performance. We can
     already measure these and see that their effect is negligible if
     any. */
  if (atomic_compare_exchange_strong_explicit(&caml_heap_table[p], &e,
                                              Unmanaged, memory_order_acq_rel,
                                              memory_order_acquire)) {
    return Unmanaged & kind;
  } else {
    // e != 0
    return e & kind;
  }
}

// Optimised for traversing the major heap
inline int caml_likely_is_in_heap(atomic_char *heap_table, value v)
{
  uintnat p = Pagetable_entry(v);
  char e = atomic_load_explicit(&heap_table[p], memory_order_relaxed);
  if (e & In_heap) return 1;
  if (LIKELY(e != 0)) return 0;
  return
    (atomic_compare_exchange_strong_explicit(&heap_table[p], &e, Unmanaged,
                                             memory_order_acq_rel,
                                             memory_order_acquire)) ?
    0 : (e & In_heap);
}

inline int caml_is_in_value_area(void *a)
{
  if (Is_in_heap_or_young(a)) return 1;
  return caml_is_in_static_data(a);
}

int caml_page_table_fault(void *addr);

int caml_page_table_add(int kind, void * start, void * end);
int caml_page_table_add_static_data(void * start, void * end);
int caml_page_table_initialize(mlsize_t bytesize);

#endif /* CAML_ADDRESS_CLASS_H */
