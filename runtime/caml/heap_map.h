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

/* Classification of pointers for runtime purposes. */

/* For efficiency, the runtime uses a heap table to classify values
   (Is_young, Is_in_heap, Is_in_value_area).

   A "foreign" pointer is a value which is a pointer, whose address
   refers to a memory range unknown to the heap table. The current
   runtime supports two different configurations that correspond to
   two different value models, depending on whether foreign pointers
   are assumed to point to well-formed blocks. A foreign pointer which
   is not a well-formed block is a "naked" pointer.

   In "classic mode", naked pointers are allowed. A valid value is
   then either:
   - a tagged integer (Is_long or !Is_block from mlvalues.h)
   - a pointer to the minor heap (Is_young)
   - a pointer to the major heap (Is_in_heap)
   - a pointer to a constant block statically-allocated by OCaml code
     or the OCaml runtime (Is_in_static_data)
   - a "foreign" pointer, which is none of the above; the destination
     of those pointers may be a well-formed OCaml blocks, but it may
     also be a naked pointer.

   The runtime conservatively assumes that all foreign pointers may be
   naked pointers, and uses the heap table to not dereference/follow
   them.

   In "no naked pointers" mode (when NO_NAKED_POINTERS is defined),
   naked pointers are illegal, and foreign pointers are assumed to
   point to well-formed blocks allocated statically. This
   corresponds to a simpler model where a valid value is either:
   - a tagged integer (Is_long)
   - a pointer to the minor heap (Is_young)
   - a pointer to a well-formed block outside the minor heap
     (it may be in the major heap, or static, or a foreign pointer).

   (To create a well-formed block outside the heap that the GC will
   not scan, one can use the Caml_out_of_heap_header from mlvalues.h.)

   It was originally assumed that removing pointer classifications
   would make the GC faster, which was an original motivation of the
   "no naked pointers" mode. But it was shown that a well-implemented
   pointer classification mechanism did not have a noticeable runtime
   cost, and in fact made the GC run slightly faster by skipping
   static data.

   A good program using exotic pointers will always declare address
   ranges in advance with the heap table, in which case the two value
   models coincide. But unfortunately for backwards-compatibility (the
   "classic mode" being the default one with OCaml 4), the semantics
   still differ for foreign pointers (e.g. for ad hoc polymorphic
   operations).
*/

#ifndef CAML_HEAP_MAP_H
#define CAML_HEAP_MAP_H

#include <assert.h>

#if (__STDC_VERSION__ >= 201112L) && !defined(__STDC_NO_ATOMICS__)
#define HAS_ATOMICS
#include <stdatomic.h>
#endif

#include "config.h"
#include "misc.h"
#include "mlvalues.h"

/* Use the following macros to test an address for the different classes
   it might belong to. */

#define Classify_addr_as(val, class)                                  \
  (CAMLassert(Is_block((value)(val))),                                \
   !!(caml_classify_address(caml_heap_table, (void*)(val)) & (class)))

#define Is_young(val) Classify_addr_as(val, In_young)
#define Is_in_heap(val) Classify_addr_as(val, In_heap)

#ifdef NO_NAKED_POINTERS

#define Is_in_heap_or_young(a) 1
#define Is_in_value_area(a) 1

#else

#define Is_in_heap_or_young(a) Classify_addr_as(a, In_heap | In_young)
#define Is_in_value_area(a)                                             \
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
#define Pagetable_entry_log 26 // 64MB
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

/*
  - We assume that synchronisation follows from ordering of control
    dependencies (Linux kernel memory model). See Paul E. McKenney, "Is
    Parallel Programming Hard, And, If So, What Can You Do About It?",
    Sections 15.2.5 & 15.3.3.
  - We do not "taint" pages containing out of heap pointers.
*/

Caml_inline int caml_classify_address(atomic_char *heap_table, void *a)
{
  intnat p = Pagetable_entry(a);
#ifdef HAS_ATOMICS
  return atomic_load_explicit(&caml_heap_table[p], memory_order_relaxed);
#else
  return caml_heap_table[p];
#endif
}

_Bool caml_is_in_static_data(void *a);

_Bool caml_heap_table_add(int kind, void *start, void *end);
_Bool caml_heap_table_add_static_data(void *start, void *end);

#ifdef CAML_INTERNALS
void caml_static_area_add(void *start, void *end);
_Bool caml_heap_table_initialize(mlsize_t bytesize);
#endif

#endif /* CAML_HEAP_MAP_H */
