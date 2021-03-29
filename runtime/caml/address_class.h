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

#include "config.h"
#include "misc.h"
#include "mlvalues.h"

/* Use the following macros to test an address for the different classes
   it might belong to. */

#define Is_young(val) \
  (CAMLassert (Is_block (val)), \
   (char *)(val) < (char *)Caml_state_field(young_end) && \
   (char *)(val) > (char *)Caml_state_field(young_start))

#ifdef NO_NAKED_POINTERS

#define Is_in_heap_or_young(a) 1
#define Is_in_value_area(a) 1

#else

#define Is_in_heap_or_young(a) (Classify_addr(a) & (In_heap | In_young))

#define Is_in_value_area(a)                                     \
  (Classify_addr(a) & (In_heap | In_young | In_static_data))

#define Is_in_static_data(a) (Classify_addr(a) & In_static_data)

#endif

/***********************************************************************/
/* The rest of this file is private and may change without notice. */

#define Not_in_heap 0
#define In_heap 1
#define In_young 2
#define In_static_data 4
#define Small_page_area 8

#define Page(p) ((uintnat) (p) >> Page_log)
#define Page_mask ((~(uintnat)0) << Page_log)
#define Large_page_log (Page_log + 6)
#define Large_page_size ((uintnat) 1 << Large_page_log)
#define Large_page_mask(p) ((uintnat) (p) & ~(Large_page_size - 1))

#ifdef ARCH_SIXTYFOUR

/* 64-bit implementation:
   The page table is represented sparsely as a hash table
   with linear probing */

struct page_table {
  mlsize_t size;                /* size == 1 << (wordsize - shift) */
  int shift;
  mlsize_t mask;                /* mask == size - 1 */
  mlsize_t occupancy;
  uintnat * entries;            /* [size]  */
};

extern struct page_table caml_page_table;

/* Page table entries are the logical 'or' of
   - the key: address of a page (low Page_log bits = 0)
   - the data: a 8-bit integer */

#define Page_entry_matches(entry,addr) \
  ((((entry) ^ (addr)) & Page_mask) == 0)

/* Multiplicative Fibonacci hashing
   (Knuth, TAOCP vol 3, section 6.4, page 518).
   HASH_FACTOR is (sqrt(5) - 1) / 2 * 2^wordsize. */
#define CAML_HASH_FACTOR 11400714819323198486UL
#define Caml_Hash(v) (((v) * CAML_HASH_FACTOR) >> caml_page_table.shift)

/* 64 bits: Represent page table as a sparse hash table */
int caml_page_table_lookup(void *addr);

#define Classify_addr(a) (caml_page_table_lookup((void *)a))

int caml_page_table_proceed(uintnat addr, uintnat *i);

inline uintnat caml_page_table_in_heap(void *addr)
{
  uintnat p = Large_page_mask(addr);
  uintnat *i = &caml_page_table.entries[Caml_Hash(Page(p))];
  uintnat e = *i;
  /* The first hit is almost always successful, so optimize for this case */
  if (LIKELY(Page_entry_matches(e,p))) return e;
  return caml_page_table_proceed(p, i);
}

#define Is_in_heap(a) (LIKELY(caml_page_table_in_heap((void *)a) & In_heap))

#else

/* 32 bits: Represent page table as a 2-level array */
#define Pagetable2_log 11
#define Pagetable2_size (1 << Pagetable2_log)
#define Pagetable1_log (Page_log + Pagetable2_log)
#define Pagetable1_size (1 << (32 - Pagetable1_log))
CAMLextern unsigned char * caml_page_table[Pagetable1_size];

#define Pagetable_index1(a) (((uintnat)(a)) >> Pagetable1_log)
#define Pagetable_index2(a) \
  ((((uintnat)(a)) >> Page_log) & (Pagetable2_size - 1))
#define Classify_addr(a) \
  caml_page_table[Pagetable_index1(a)][Pagetable_index2(a)]
#define Is_in_heap(a) (Classify_addr(a) & In_heap)

#endif

int caml_page_table_add(int kind, void * start, void * end);
int caml_page_table_remove(int kind, void * start, void * end);
int caml_page_table_initialize(mlsize_t bytesize);

#endif /* CAML_ADDRESS_CLASS_H */
