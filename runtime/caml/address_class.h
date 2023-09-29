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

   Note that contrary to expectations, without a page table the GC is
   slightly slower, because an optimised page table check is
   fast-enough that the time gained by not visiting static data for
   marking becomes predominant. There is no more good reasons to adapt
   programs to the NO_NAKED_POINTERS mode, but unfortunately the
   semantics still differ (e.g. for ad hoc polymorphic operations).
   (Note: one solution could be to change the page table to respect
   the specification "unannounced pointers are assumed static" in the
   future---dynamic allocation off-heap must be announced beforehand.)
*/

#ifndef CAML_ADDRESS_CLASS_H
#define CAML_ADDRESS_CLASS_H

#include <assert.h>

#if (__STDC_VERSION__ >= 201112L) && !defined(__STDC_NO_ATOMICS__)
#define HAS_ATOMICS
#include <stdatomic.h>
#endif

#include "config.h"
#include "misc.h"
#include "mlvalues.h"
#include "page_allocator.h"

/* Use the following macros to test an address for the different classes
   it might belong to. */

#define Is_young(val) \
  (CAMLassert (Is_block (val)), \
   (char *)(val) < (char *)Caml_state_field(young_alloc_end) && \
   (char *)(val) > (char *)Caml_state_field(young_alloc_start))

#define Is_in_heap(a) (caml_classify_address((void*)a) & In_heap)

#ifdef NO_NAKED_POINTERS

#define Is_in_heap_or_young(a) 1
#define Is_in_value_area(a) 1

#else

#define Is_in_heap_or_young(a)                              \
  (caml_classify_address((void*)a) & (In_heap | In_young))

#define Is_in_value_area(a) \
  (Is_in_heap_or_young(a) || caml_is_in_static_data((void *)(a)))

#endif /* NO_NAKED_POINTERS */

/***********************************************************************/
/* The rest of this file is private and may change without notice. */

#define In_heap 1
#define In_young 2
#define Unmanaged 4

/* Page table: bibop */

/* Granularity for VAS reservations */
#ifdef ARCH_SIXTYFOUR
#define Pagetable_entry_log                                     \
  (Page_allocator_significant_ptr_bits - 22) // 64MB for 48bits
#else
#define Pagetable_entry_log 22 // 4MB
#endif /* ARCH_SIXTYFOUR */

#define Pagetable_entry_size ((intnat)1 << Pagetable_entry_log)
#define TBI 0
/*
#define TBI 8 // Arm TBI
#define TBI 7 // Intel LAM_U57 / AMD UAI
#define TBI 16 // Intel LAM_U48
*/
#define Pagetable_entry(p) (((intnat)(p) << TBI) >> (TBI + Pagetable_entry_log))

#ifndef HAS_ATOMICS
typedef char atomic_char;
#endif
CAMLextern atomic_char *caml_heap_table;

Caml_inline char caml_heap_table_get_sync(intnat p)
{
  char e = 0;
#ifdef HAS_ATOMICS
  if (atomic_compare_exchange_strong_explicit(&caml_heap_table[p], &e,
                                              Unmanaged, memory_order_acq_rel,
                                              memory_order_acquire)) {
#else
  if (e = caml_heap_table[p], e == 0) {
    caml_heap_table[p] = Unmanaged;
#endif
    return Unmanaged;
  } else {
    // e != 0
    return e;
  }
}

Caml_inline int caml_classify_address(void *a)
{
  intnat p = Pagetable_entry(a);
#ifdef HAS_ATOMICS
  char e = atomic_load_explicit(&caml_heap_table[p], memory_order_relaxed);
#else
  char e = caml_heap_table[p];
#endif
  if (CAMLlikely(e != 0)) return e;
  return caml_heap_table_get_sync(p);
}

/*
  - We assume that synchronisation follows from ordering of control
    dependencies (Linux kernel memory model). See Paul E. McKenney, "Is
    Parallel Programming Hard, And, If So, What Can You Do About It?",
    Sections 15.2.5 & 15.3.3.
  - We do not "taint" pages containing out of heap pointers.
*/
Caml_inline int caml_in_heap_cached(value v, atomic_char *heap_table)
{
  intnat p = Pagetable_entry(v);
#ifdef HAS_ATOMICS
  char e = atomic_load_explicit(&heap_table[p], memory_order_relaxed);
#else
  char e = heap_table[p];
#endif
  return CAMLlikely(e & In_heap);
}

int caml_is_in_static_data(void *a);

int caml_page_table_add(int kind, void * start, void * end);
int caml_page_table_add_static_data(void * start, void * end);

#ifdef CAML_INTERNALS
int caml_page_table_initialize(mlsize_t bytesize);
#endif

#endif /* CAML_ADDRESS_CLASS_H */
