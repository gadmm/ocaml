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

#define CAML_INTERNALS

#include <assert.h>
#include <errno.h>
#include <stdlib.h>
#include <stdatomic.h>
#include <string.h>
#include <stdarg.h>
#include <stddef.h>
#include <unistd.h>
#include <sys/mman.h>
#include "caml/address_class.h"
#include "caml/config.h"
#include "caml/fail.h"
#include "caml/freelist.h"
#include "caml/gc.h"
#include "caml/gc_ctrl.h"
#include "caml/major_gc.h"
#include "caml/memory.h"
#include "caml/major_gc.h"
#include "caml/minor_gc.h"
#include "caml/misc.h"
#include "caml/mlvalues.h"
#include "caml/signals.h"
#include "caml/skiplist.h"
#include "caml/memprof.h"
#include "caml/eventlog.h"

uintnat caml_use_huge_pages = 0;
/* True iff the program allocates heap chunks by mmapping huge pages.
   This is set when parsing [OCAMLRUNPARAM] and must stay constant
   after that.
*/

extern uintnat caml_percent_free;                   /* major_gc.c */

/* Page table management */

atomic_char *caml_heap_table = NULL;
uintnat caml_real_page_size = 0;

#define Pagetable_log (Pagetable_significant_bits - Pagetable_entry_log) // 20
#define Pagetable_size (((uintnat)1 << Pagetable_log))

// TODO: better portability of on-demand paging
#if (defined(NATIVE_CODE) && defined(POSIX_SIGNALS))
#define PAGE_TABLE_ON_DEMAND 1
#else
#define PAGE_TABLE_ON_DEMAND 0
#endif

int caml_page_table_initialize(mlsize_t bytesize)
{
#if PAGE_TABLE_ON_DEMAND
  // 2^(Pagetable_log - Page_log) = 1MB paged on demand.
  int prot = PROT_NONE;
#else
  // 2^(Pagetable_log - Page_log) = 1MB initially mapped to the zero
  // page and:
  // - allocated on demand if overcommitting is enabled,
  // - committed up-front otherwise.
  // (bytecode)
  int prot = PROT_READ | PROT_WRITE;
#endif
  // TODO: win32
  void *block = mmap(NULL, Pagetable_size, prot,
                     MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  if (block == MAP_FAILED) return -1;
  caml_heap_table = (atomic_char *)block;
  caml_real_page_size = sysconf(_SC_PAGESIZE);
  CAMLassert(caml_real_page_size >= Page_size);
  return 0;
  // TODO: free on shutdown
}

#define CAMLassert_aligned_(n, m)                     \
  (CAMLassert(((uintnat)n & ((uintnat)m - 1)) == 0))
#define CAMLassert_aligned(n, m)                          \
  (CAMLassert_is_power_of_2(m),CAMLassert_aligned_(n,m))
#define CAMLassert_is_power_of_2(n) CAMLassert_aligned_(n, n)

static uintnat round_up(uintnat n, uintnat mod)
{
  return (n + mod - 1) / mod * mod;
}

/* This is called infrequently, and for a small portion of
   caml_heap_table, thanks to the hints given to mmap inside
   [caml_alloc_for_heap] which tends to reserve heap inside
   already-committed pages of caml_heap_table. Must be
   async-signal-safe.*/
static int page_table_commit(uintnat start, uintnat end)
{
  int ret = 0;
#if PAGE_TABLE_ON_DEMAND
  uintnat page_start = start & Real_page_mask;
  uintnat page_end = round_up(end, Real_page_size);
  uintnat size = page_end - page_start;
  CAMLassert(page_end <= Pagetable_size);
  ret = mprotect(&caml_heap_table[page_start], size, PROT_READ | PROT_WRITE);
  CAMLassert(ret != -1 || errno == ENOMEM);
#endif
  return ret;
}

/* Function called from a signal handler. It must be
   async-signal-safe. Returns 1 if the fault is due to a naked pointer
   caught for the first time inside the address space described by
   this caml_heap_table page. Returns 0 if the fault is unrelated.
   Happens less than 255 times over the execution of a program.
*/
int caml_page_table_fault(void *addr)
{
  uintnat p = (uintnat)addr;
  // If outside of the page table, it is not ours
  if (p < (uintnat)caml_heap_table ||
      p >= (uintnat)caml_heap_table + Pagetable_size)
    return 0;
  // Allocate a page of the heap table.
  if (-1 == page_table_commit(p, p + 1)) {
    // We assume that this call is safe because we cause the fault in
    // places in the runtime that are safe for functions like malloc,
    // printf... and the program execution will end immediately
    // afterwards. We make the same assumption for the asserts inside
    // page_table_commit.
    caml_fatal_error("out of memory");
  }
  return 1;
}

// Assumes that the caller owns the mapping from start to end, to
// ensure that we are not racing to set the same entry twice.
// Idempotent (returns 0 even if some page table entries are already
// set to [kind]).
int caml_page_table_add(int kind, void * start, void * end)
{
  uintnat pstart = Pagetable_entry(start);
  uintnat pend = Pagetable_entry((uintnat)end - 1) + 1;
  uintnat p;
  int ret = 0;
  if (-1 == page_table_commit(pstart, pend)) return -1;
  for (p = pstart; p < pend; p++) {
    char e = 0;
    if (!atomic_compare_exchange_strong_explicit(&caml_heap_table[p], &e,
                                                 kind, memory_order_acq_rel,
                                                 memory_order_acquire))
      // It is a programming error to:
      // - Let foreign pointers be seen by the OCaml GC
      // - Release the underlying mapping of these pointers, so that
      //   the same virtual space can later be acquired by the runtime.
      //
      // However we could be more lenient and just find someplace else
      // (in situations where the world declares their pages of
      // interest to OCaml in advance, they can free the mapping and
      // we know to avoid this range). This just needs a third error
      // value and to adjust the callers.
      //
      // This is to ensure that the heap table is monotonic. This is
      // not a safety measure (there is no guarantee that the GC has
      // the time to see all the naked pointers before OCaml acquires
      // the mapping, except in situations where the world declared
      // their pages of interest in advances).
      if (e != kind) ret = -1;
  }
  return ret;
}

/* Reservation, platform-specific */

static void mem_unmap_os(char *block, asize_t size)
{
  if (size != 0) munmap(block, size);
}

/* Reserve memory, aligned at Pagetable_entry_size. [size] must be a
   multiple of Pagetable_entry_size. */
char * caml_mem_reserve_os(asize_t size)
{
  // All platforms except win32. TODO: see golang for win32.
  static char *last_mem = NULL;
  static asize_t last_size = 0;
  char *mem;
  char *block;
  asize_t request_virtual = size + Pagetable_entry_size;
  CAMLassert_aligned(size, Pagetable_entry_size);
  // Hint at the end of the previously-reserved block
  block = mmap(last_mem + last_size, request_virtual, PROT_NONE,
               MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  if (block == MAP_FAILED) return NULL;
  // Prefer contiguous if possible, to avoid holes in the VAS
  if (block + request_virtual == last_mem) {
    // On Linux, the mmaped area grows downwards
    mem = last_mem - size;
  } else {
    mem = (char *) round_up((uintnat)block, Pagetable_entry_size);
  }
  CAMLassert((uintnat) mem + size <= (uintnat) block + request_virtual);
  /* free beginning */
  mem_unmap_os(block, mem - block);
  /* free end */
  mem_unmap_os(mem + size, request_virtual - (mem - block) - size);
  /* [mem..mem+size[ is reserved */
  last_mem = mem;
  last_size = size;
  return mem;
}

static int madvise_os(char *block, asize_t size, int madvice)
{
  int err;
  // EAGAIN is Linux-specific
  while (-1 == (err = madvise(block, size, madvice)) && errno == EAGAIN) {};
  return err;
}

// can be used to recommit (does not destroy already-committed mapping)
int caml_mem_commit_os(char *block, asize_t size)
{
  // - Commit:
  //    - Ensure it fails on OOM if overcommitting is off.
  //    - MADV_FREE_REUSE on Darwin
  //    - MADV_DODUMP, MADV_CORE. Darwin: none.
  CAMLassert_aligned(block, Huge_page_size);
  CAMLassert_aligned(size, Real_page_size);
  if (-1 == mprotect(block, size, PROT_READ | PROT_WRITE)) return -1;
  /* MADV_DODUMP: cancel MADV_DONTDUMP */
  if (-1 == madvise_os(block, size, MADV_DODUMP)) return -1;
#ifdef MADV_HUGEPAGE
  if (caml_use_huge_pages) {
    CAMLassert_aligned(size, Huge_page_size);
    /* Request huge pages (THP) if huge pages are enabled. Note: this
       can cause large pauses if /sys/kernel/mm/transparent_hugepage/defrag
       is set to [always], [madvise] or [defer+madvise], since OCaml
       will try to touch a lot of huge pages at once. [defer] is
       preferred. */
    if (-1 == madvise_os(block, size, MADV_HUGEPAGE)) return -1;
    /* TODO:
       - 1GB hugepage support.
       - restore hugetlb behaviour for backwards-compat. */
  }
#endif
  return 0;
}

void caml_mem_decommit_os(char * block, asize_t size)
{
  // - Decommit:
  //    - MADV_DONTNEED on Linux with overcommitting, MADV_FREE on BSD
  //      and Haiku, MADV_FREE_REUSABLE on Darwin, MADV_DONTNEED as a
  //      fallback, posix_madvise & POSIX_MADV_DONTNEED as a fallback?
  //    - mmap(PROT_NONE,MAP_FIXED) to decommit in Linux without
  //      overcommitting (see jemalloc,glibc malloc)
  //      (https://github.com/bminor/glibc/commit/9fab36eb58)
  //    - MADV_FREE exists on Linux, so be careful about #ifdef.
  //    - MADV_DONTDUMP on Linux, MADV_NOCORE on BSD. (Not needed for
  //      core files, but seems to help gdb) Darwin: NONE
  if (size == 0) return;
  CAMLassert_aligned(block, Real_page_size);
  CAMLassert_aligned(size, Real_page_size);
  mprotect(block, size, PROT_NONE);
  madvise_os(block, size, MADV_DONTNEED);
  madvise_os(block, size, MADV_DONTDUMP);
}


/* Reserving, committing, decommitting. Platform-independent. */


/* Heuristic to round up to the nearest small page or huge page,
   depending on what is best. */
asize_t caml_round_up_to_huge_page(asize_t size)
{
  asize_t page_size = caml_use_huge_pages ?
    Huge_page_size : Real_page_size;
  return round_up(size, page_size);
}

// reserve at least [request] contiguous memory and record it with the
// page table.
int caml_mem_reserve(asize_t request, int kind,
                     char **out_block, asize_t *out_reserved)
{
  char *mem;
  request = round_up(request, Pagetable_entry_size);
  /* hint at reserving near the previous block to
     have a good location in the page table. */
  mem = caml_mem_reserve_os(request);
  if (mem == NULL) return -1;
  *out_block = mem;
  *out_reserved = request;
  /* keep reserved in case of error of the page table */
  return caml_page_table_add(kind, mem, mem + request);
}

/* [block] must be aligned to huge pages, and there must be enough
   space to round request up to the nearest page or huge page. If
   successful, [out_size] is set to the size that was actually
   committed. */
int caml_mem_commit(char *block, asize_t request, asize_t *out_size)
{
  request = caml_round_up_to_huge_page(request);
  /* Commit [block..block+size[ */
  if (-1 == caml_mem_commit_os(block, request)) goto err;
  *out_size = request;
  return 0;
err:
  caml_mem_decommit_os(block, request);
  return -1;
}

/* [block] and [size] must be aligned to Real_page_size. */
void caml_mem_decommit(char * block, asize_t size)
{
  caml_mem_decommit_os(block, size);
}


/* A best-fit allocator for reserved virtual address space */

typedef struct {
  int const page_log;
  /* size of pages managed, typically Huge_page_log or Page_log */
  struct skiplist free_per_address_sk;
  /* address of each allocated block and its size */
  struct skiplist free_per_size_sk;
  /* each allocated block ordered per decreasing size.

     key: lexicographic ordering by size (decreasing) and address.

       ~( # huge pages )      msbs of address
     |-------------------|------------------------|
        num_max_log bits   small_address_log bits
  */
} page_allocator;

#define PA_STATIC_INITIALIZER(page_log) \
  { page_log, SKIPLIST_STATIC_INITIALIZER, SKIPLIST_STATIC_INITIALIZER }

#define PA_page_size(pa) ((uintnat)1 << pa->page_log)
#define PA_small_address_log(pa) (Pagetable_significant_bits - pa->page_log)
#define PA_small_address_mask(pa) (((uintnat)1 << PA_small_address_log(pa)) - 1)
#define PA_num_max_log(pa) (8 * sizeof(uintnat) - PA_small_address_log(pa))
#define PA_size_max(pa) \
  ((((uintnat)1 << PA_num_max_log(pa)) - 1) << pa->page_log)

static uintnat pa_size_key(page_allocator *pa, char *block, asize_t size)
{
  uintnat compl_num_elems;
  uintnat small_address;
  CAMLassert_aligned(size, PA_page_size(pa));
  CAMLassert_aligned(block, PA_page_size(pa));
  CAMLassert(size <= PA_size_max(pa));
  compl_num_elems = ~((uintnat)size >> pa->page_log);
  compl_num_elems <<= PA_small_address_log(pa);
  if (block != NULL) {
    // address of the mapping
    small_address =
      ((uintnat)block >> pa->page_log) & PA_small_address_mask(pa);
  } else {
    // greater than any address
    small_address = PA_small_address_mask(pa);
  }
  return compl_num_elems + small_address;
}

// assumes (block, size) is a member of the freelist
static void pa_remove_free(page_allocator *pa, char *block, asize_t size)
{
  uintnat key = pa_size_key(pa, block, size);
  caml_skiplist_remove(&pa->free_per_address_sk, (uintnat)block)
    ?: CAMLassert(0);
  caml_skiplist_remove(&pa->free_per_size_sk, key) ?: CAMLassert(0);
}

// assumes (block, size) is not a member of the freelist and size < Size_max.
static void pa_add_free(page_allocator *pa, char *block, asize_t size)
{
  caml_skiplist_insert(&pa->free_per_address_sk, (uintnat)block, (uintnat)size);
  caml_skiplist_insert(&pa->free_per_size_sk, pa_size_key(pa, block, size),
                       (uintnat)block);
}

static int pa_find_address(page_allocator *pa, char *block, asize_t *size_out)
{
  return caml_skiplist_find(&pa->free_per_address_sk, (uintnat)block, size_out);
}

Caml_inline int pa_find_below_address(page_allocator *pa, char *addr,
                                      char **block_out, asize_t *size_out)
{
  uintnat address;
  if (caml_skiplist_find_below(&pa->free_per_address_sk, (uintnat)addr,
                               &address, size_out)) {
    *block_out = (char *)address;
    return 1;
  }
  return 0;
}

/* size <= PA_size_max */
static int pa_find_above_size(page_allocator *pa, asize_t size,
                              char **block_out, asize_t *available_out)
{
  uintnat key, address;
  if (caml_skiplist_find_below(&pa->free_per_size_sk,
                               pa_size_key(pa, NULL, size),
                               &key, &address)) {
    *block_out = (char *)address;
    pa_find_address(pa, *block_out, available_out) ?: CAMLassert(0);
    return 1;
  }
  return 0;
}

/* (block, size) must not overlap with existing ranges in the
   allocator. */
static void pa_merge(page_allocator *pa, char *block, asize_t size)
{
  char *block_before;
  char *block_after = block + size;
  asize_t size_before, size_after;
  // Merge with block before
  if (pa_find_below_address(pa, block, &block_before, &size_before)) {
    if (block_before + size_before == block
        && size + size_before <= PA_size_max(pa)) {
      pa_remove_free(pa, block_before, size_before);
      block = block_before;
      size += size_before;
    }
  }
  // Merge with block after
  if (pa_find_address(pa, block_after, &size_after)
      && size + size_after <= PA_size_max(pa)) {
    pa_remove_free(pa, block_after, size_after);
    size += size_after;
  }
  pa_add_free(pa, block, size);
}

#define MMAP_GROWS_DOWN 1

// returns 1 on success, 0 if out of reserved space
static int pa_alloc(page_allocator *pa, asize_t request,
                    char **block_out, asize_t *size_out)
{
  char *block;
  asize_t available;
  request = round_up(request, PA_page_size(pa));
  if (pa_find_above_size(pa, request, &block, &available)) {
    char *new_block;
    pa_remove_free(pa, block, available);
    if (MMAP_GROWS_DOWN) {
      new_block = block + available - request;
    } else {
      new_block = block;
      block += request;
    }
    available -= request;
    pa_add_free(pa, block, available);
    *size_out = request;
    *block_out = new_block;
    return 1;
  } else {
    return 0;
  }
}

CAMLunused_start
static void pa_debug(page_allocator *pa)
CAMLunused_end
{
  int num = 0;
  FOREACH_SKIPLIST_ELEMENT(var, &pa->free_per_address_sk, {
      char *beg = (char *)var->key;
      asize_t size = var->data;
      fprintf(stderr, "(%p, %d pages)", beg, (int)(size / PA_page_size(pa)));
      if (!caml_skiplist_find(&pa->free_per_size_sk,
                              pa_size_key(pa, beg, size), &size)
          && size != var->data)
        fprintf(stderr, "corrupt ");
      num++;
    });
  FOREACH_SKIPLIST_ELEMENT(var, &pa->free_per_size_sk, { num--; });
  if (num != 0) fprintf(stderr, "num mismatch");
  fprintf(stderr, "\n");
}

/* Static data table */

static page_allocator static_area = PA_STATIC_INITIALIZER(Page_log);

int caml_is_in_static_data(void *addr)
{
  char *block;
  asize_t size;
  return pa_find_below_address(&static_area, (char *)addr, &block, &size)
    && (char *)addr < block + size;
}

static void static_area_insert(void * start, void * end)
{
  uintnat pstart = (uintnat)start & Page_mask;
  uintnat pend = ((uintnat)end - 1) & Page_mask;
  uintnat addr;
  for (addr = pstart; addr <= pend; addr += Page_size) {
    char *p = (char *)addr;
    if (!caml_is_in_static_data(p))
      pa_merge(&static_area, p, Page_size);
  }
}

int caml_page_table_add_static_data(void * start, void * end)
{
  if (-1 == caml_page_table_add(Unmanaged, start, end))
    return -1;
  static_area_insert(start, end);
//  fprintf(stderr, "Static data: ");
//  pa_debug(&static_area);
  return 0;
}

/* VAS allocator for the major heap */

static page_allocator heap_allocator = PA_STATIC_INITIALIZER(Huge_page_log);

int caml_heap_commit(asize_t request, char **out_block,
                     asize_t *out_size, asize_t *out_reserved)
{
  char *block;
  asize_t reserved;
  if (!pa_alloc(&heap_allocator, request, &block, &reserved)) {
    // Out of already-reserved space
    char *mem;
    asize_t new_reserve;
    // Reserve a large-enough space
    // TODO: unmap on shutdown
    if (-1 == caml_mem_reserve(request, In_heap, &mem, &new_reserve))
      return -1;
    pa_merge(&heap_allocator, mem, new_reserve);
    // Now it should succeed
    pa_alloc(&heap_allocator, request, &block, &reserved) ?: CAMLassert(0);
  }
//  fprintf(stderr, "Heap reserved: ");
//  pa_debug(&heap_allocator);
  if (-1 == caml_mem_commit(block, request, &request)) goto err;
  *out_block = block;
  *out_size = request;
  *out_reserved = reserved;
  return 0;
err:
  pa_merge(&heap_allocator, block, reserved);
  return -1;
}

void caml_heap_decommit(char * block, asize_t size)
{
  caml_mem_decommit(block, size);
  pa_merge(&heap_allocator, block, size);
//  fprintf(stderr, "Heap reserved: ");
//  pa_debug(&heap_allocator);
}

/* Allocate a block of the requested size, to be passed to
   [caml_add_to_heap] later.
   [request] will be rounded up to some implementation-dependent size.
   The caller must use [Chunk_size] on the result to recover the actual
   size.
   Return NULL if the request cannot be satisfied. The returned pointer
   is a hp, but the header (and the contents) must be initialized by the
   caller.
*/
char *caml_alloc_for_heap (asize_t request)
{
  // TODO: free on shutdown
  char *mem, *block;
  asize_t reserved, committed;
  request += sizeof(heap_chunk_head);
  if (-1 == caml_heap_commit(request, &block, &committed, &reserved))
    return NULL;
  mem = block + sizeof(heap_chunk_head);
  Chunk_size(mem) = committed - sizeof(heap_chunk_head);
  Chunk_block(mem) = block;
  Chunk_block_size(mem) = reserved;
  Chunk_head (mem)->redarken_first.start = (value*)(mem + Chunk_size(mem));
  Chunk_head (mem)->redarken_first.end = (value*)(mem + Chunk_size(mem));
  Chunk_head (mem)->redarken_end = (value*)mem;
  return mem;
}

/* Use this function to free a block allocated with
   [caml_alloc_for_heap] if you don't add it with [caml_add_to_heap].
*/
void caml_free_for_heap (char *mem)
{
  caml_heap_decommit(Chunk_block(mem), Chunk_block_size(mem));
}

/* Take a chunk of memory as argument, which must be the result of a
   call to [caml_alloc_for_heap], and insert it into the heap chaining.
   The contents of the chunk must be a sequence of valid blocks and
   fragments: no space between blocks and no trailing garbage.  If
   some blocks are blue, they must be added to the free list by the
   caller.  All other blocks must have the color [caml_allocation_color(m)].
   The caller must update [caml_allocated_words] if applicable.
   Return value: 0 if no error; -1 in case of error.

   See also: caml_compact_heap, which duplicates most of this function.
*/
int caml_add_to_heap (char *m)
{
#ifdef DEBUG
  /* Should check the contents of the block. */
#endif /* DEBUG */

  caml_gc_message (0x04, "Growing heap to %"
                   ARCH_INTNAT_PRINTF_FORMAT "uk bytes\n",
     (Bsize_wsize (Caml_state->stat_heap_wsz) + Chunk_size (m)) / 1024);

  /* Register block in page table */
  if (caml_page_table_add(In_heap, m, m + Chunk_size(m)) != 0)
    return -1;

  /* Chain this heap chunk. */
  {
    char **last = &caml_heap_start;
    char *cur = *last;

    while (cur != NULL && cur < m){
      last = &(Chunk_next (cur));
      cur = *last;
    }
    Chunk_next (m) = cur;
    *last = m;

    ++ Caml_state->stat_heap_chunks;
  }

  Caml_state->stat_heap_wsz += Wsize_bsize (Chunk_size (m));
  if (Caml_state->stat_heap_wsz > Caml_state->stat_top_heap_wsz){
    Caml_state->stat_top_heap_wsz = Caml_state->stat_heap_wsz;
  }
  return 0;
}

/* Allocate more memory from malloc for the heap.
   Return a blue block of at least the requested size.
   The blue block is chained to a sequence of blue blocks (through their
   field 0); the last block of the chain is pointed by field 1 of the
   first.  There may be a fragment after the last block.
   The caller must insert the blocks into the free list.
   [request] is a number of words and must be less than or equal
   to [Max_wosize].
   Return NULL when out of memory.
*/
static value *expand_heap (mlsize_t request)
{
  /* these point to headers, but we do arithmetic on them, hence [value *]. */
  value *mem, *hp, *prev;
  asize_t over_request, malloc_request, remain;

  CAMLassert (request <= Max_wosize);
  over_request = request + request / 100 * caml_percent_free;
  malloc_request = caml_clip_heap_chunk_wsz (over_request);
  mem = (value *) caml_alloc_for_heap (Bsize_wsize (malloc_request));
  if (mem == NULL){
    caml_gc_message (0x04, "No room for growing heap\n");
    return NULL;
  }
  remain = Wsize_bsize (Chunk_size (mem));
  prev = hp = mem;
  /* FIXME find a way to do this with a call to caml_make_free_blocks */
  while (Wosize_whsize (remain) > Max_wosize){
    Hd_hp (hp) = Make_header (Max_wosize, 0, Caml_blue);
#ifdef DEBUG
    caml_set_fields (Val_hp (hp), 0, Debug_free_major);
#endif
    hp += Whsize_wosize (Max_wosize);
    remain -= Whsize_wosize (Max_wosize);
    Field (Val_hp (mem), 1) = Field (Val_hp (prev), 0) = Val_hp (hp);
    prev = hp;
  }
  if (remain > 1){
    Hd_hp (hp) = Make_header (Wosize_whsize (remain), 0, Caml_blue);
#ifdef DEBUG
    caml_set_fields (Val_hp (hp), 0, Debug_free_major);
#endif
    Field (Val_hp (mem), 1) = Field (Val_hp (prev), 0) = Val_hp (hp);
    Field (Val_hp (hp), 0) = (value) NULL;
  }else{
    Field (Val_hp (prev), 0) = (value) NULL;
    if (remain == 1) {
      Hd_hp (hp) = Make_header (0, 0, Caml_white);
    }
  }
  CAMLassert (Wosize_hp (mem) >= request);
  if (caml_add_to_heap ((char *) mem) != 0){
    caml_free_for_heap ((char *) mem);
    return NULL;
  }
  return Op_hp (mem);
}

/* Remove the heap chunk [chunk] from the heap and give the memory back
   to [free].
*/
void caml_shrink_heap (char *chunk)
{
  char **cp;

  /* Never deallocate the first chunk, because caml_heap_start is both the
     first block and the base address for page numbers, and we don't
     want to shift the page table, it's too messy (see above).
     It will never happen anyway, because of the way compaction works.
     (see compact.c)
     XXX FIXME this has become false with the fix to PR#5389 (see compact.c)
  */
  if (chunk == caml_heap_start) return;

  Caml_state->stat_heap_wsz -= Wsize_bsize (Chunk_size (chunk));
  caml_gc_message (0x04, "Shrinking heap to %"
                   ARCH_INTNAT_PRINTF_FORMAT "dk words\n",
                   Caml_state->stat_heap_wsz / 1024);

#ifdef DEBUG
  {
    mlsize_t i;
    for (i = 0; i < Wsize_bsize (Chunk_size (chunk)); i++){
      ((value *) chunk) [i] = Debug_free_shrink;
    }
  }
#endif

  -- Caml_state->stat_heap_chunks;

  /* Remove [chunk] from the list of chunks. */
  cp = &caml_heap_start;
  while (*cp != chunk) cp = &(Chunk_next (*cp));
  *cp = Chunk_next (chunk);

  /* Free the [malloc] block that contains [chunk]. */
  caml_free_for_heap (chunk);
}

CAMLexport color_t caml_allocation_color (void *hp)
{
  if (caml_gc_phase == Phase_mark || caml_gc_phase == Phase_clean ||
      (caml_gc_phase == Phase_sweep && (char *)hp >= (char *)caml_gc_sweep_hp)){
    return Caml_black;
  }else{
    CAMLassert (caml_gc_phase == Phase_idle
            || (caml_gc_phase == Phase_sweep
                && (char *)hp < (char *)caml_gc_sweep_hp));
    return Caml_white;
  }
}

Caml_inline value caml_alloc_shr_aux (mlsize_t wosize, tag_t tag, int track,
                                      uintnat profinfo)
{
  header_t *hp;
  value *new_block;

  if (wosize > Max_wosize) return 0;
  CAML_EV_ALLOC(wosize);
  hp = caml_fl_allocate (wosize);
  if (hp == NULL){
    new_block = expand_heap (wosize);
    if (new_block == NULL) return 0;
    caml_fl_add_blocks ((value) new_block);
    hp = caml_fl_allocate (wosize);
  }

  CAMLassert (Is_in_heap (Val_hp (hp)));

  /* Inline expansion of caml_allocation_color. */
  if (caml_gc_phase == Phase_mark || caml_gc_phase == Phase_clean ||
      (caml_gc_phase == Phase_sweep && (char *)hp >= (char *)caml_gc_sweep_hp)){
    Hd_hp (hp) = Make_header_with_profinfo (wosize, tag, Caml_black, profinfo);
  }else{
    CAMLassert (caml_gc_phase == Phase_idle
            || (caml_gc_phase == Phase_sweep
                && (char *)hp < (char *)caml_gc_sweep_hp));
    Hd_hp (hp) = Make_header_with_profinfo (wosize, tag, Caml_white, profinfo);
  }
  CAMLassert (Hd_hp (hp)
    == Make_header_with_profinfo (wosize, tag, caml_allocation_color (hp),
                                  profinfo));
  caml_allocated_words += Whsize_wosize (wosize);
  if (caml_allocated_words > Caml_state->minor_heap_wsz){
    CAML_EV_COUNTER (EV_C_REQUEST_MAJOR_ALLOC_SHR, 1);
    caml_request_major_slice ();
  }
#ifdef DEBUG
  {
    uintnat i;
    for (i = 0; i < wosize; i++){
      Field (Val_hp (hp), i) = Debug_uninit_major;
    }
  }
#endif
  if(track)
    caml_memprof_track_alloc_shr(Val_hp (hp));
  return Val_hp (hp);
}

Caml_inline value check_oom(value v)
{
  if (v == 0) {
    if (Caml_state->in_minor_collection)
      caml_fatal_error ("out of memory");
    else
      caml_raise_out_of_memory ();
  }
  return v;
}

CAMLexport value caml_alloc_shr_with_profinfo (mlsize_t wosize, tag_t tag,
                                               intnat profinfo)
{
  return check_oom(caml_alloc_shr_aux(wosize, tag, 1, profinfo));
}

CAMLexport value caml_alloc_shr_for_minor_gc (mlsize_t wosize,
                                              tag_t tag, header_t old_hd)
{
  return check_oom(caml_alloc_shr_aux(wosize, tag, 0, Profinfo_hd(old_hd)));
}

CAMLexport value caml_alloc_shr (mlsize_t wosize, tag_t tag)
{
  return caml_alloc_shr_with_profinfo(wosize, tag, NO_PROFINFO);
}

CAMLexport value caml_alloc_shr_no_track_noexc (mlsize_t wosize, tag_t tag)
{
  return caml_alloc_shr_aux(wosize, tag, 0, NO_PROFINFO);
}

/* Dependent memory is all memory blocks allocated out of the heap
   that depend on the GC (and finalizers) for deallocation.
   For the GC to take dependent memory into account when computing
   its automatic speed setting,
   you must call [caml_alloc_dependent_memory] when you allocate some
   dependent memory, and [caml_free_dependent_memory] when you
   free it.  In both cases, you pass as argument the size (in bytes)
   of the block being allocated or freed.
*/
CAMLexport void caml_alloc_dependent_memory (mlsize_t nbytes)
{
  caml_dependent_size += nbytes / sizeof (value);
  caml_dependent_allocated += nbytes / sizeof (value);
}

CAMLexport void caml_free_dependent_memory (mlsize_t nbytes)
{
  if (caml_dependent_size < nbytes / sizeof (value)){
    caml_dependent_size = 0;
  }else{
    caml_dependent_size -= nbytes / sizeof (value);
  }
}

/* Use this function to tell the major GC to speed up when you use
   finalized blocks to automatically deallocate resources (other
   than memory). The GC will do at least one cycle every [max]
   allocated resources; [res] is the number of resources allocated
   this time.
   Note that only [res/max] is relevant.  The units (and kind of
   resource) can change between calls to [caml_adjust_gc_speed].
*/
CAMLexport void caml_adjust_gc_speed (mlsize_t res, mlsize_t max)
{
  if (max == 0) max = 1;
  if (res > max) res = max;
  caml_extra_heap_resources += (double) res / (double) max;
  if (caml_extra_heap_resources > 1.0){
    CAML_EV_COUNTER (EV_C_REQUEST_MAJOR_ADJUST_GC_SPEED, 1);
    caml_extra_heap_resources = 1.0;
    caml_request_major_slice ();
  }
}

/* You must use [caml_initialize] to store the initial value in a field of
   a shared block, unless you are sure the value is not a young block.
   A block value [v] is a shared block if and only if [Is_in_heap (v)]
   is true.
*/
/* [caml_initialize] never calls the GC, so you may call it while a block is
   unfinished (i.e. just after a call to [caml_alloc_shr].) */
/* PR#6084 workaround: define it as a weak symbol */
CAMLexport CAMLweakdef void caml_initialize (value *fp, value val)
{
  CAMLassert(Is_in_heap_or_young(fp));
  *fp = val;
  if (!Is_young((value)fp) && Is_block (val) && Is_young (val)) {
    add_to_ref_table (Caml_state->ref_table, fp);
  }
}

/* You must use [caml_modify] to change a field of an existing shared block,
   unless you are sure the value being overwritten is not a shared block and
   the value being written is not a young block. */
/* [caml_modify] never calls the GC. */
/* [caml_modify] can also be used to do assignment on data structures that are
   in the minor heap instead of in the major heap.  In this case, it
   is a bit slower than simple assignment.
   In particular, you can use [caml_modify] when you don't know whether the
   block being changed is in the minor heap or the major heap. */
/* PR#6084 workaround: define it as a weak symbol */

CAMLexport CAMLweakdef void caml_modify (value *fp, value val)
{
  /* The write barrier implemented by [caml_modify] checks for the
     following two conditions and takes appropriate action:
     1- a pointer from the major heap to the minor heap is created
        --> add [fp] to the remembered set
     2- a pointer from the major heap to the major heap is overwritten,
        while the GC is in the marking phase
        --> call [caml_darken] on the overwritten pointer so that the
            major GC treats it as an additional root.

     The logic implemented below is duplicated in caml_array_fill to
     avoid repeated calls to caml_modify and repeated tests on the
     values.  Don't forget to update caml_array_fill if the logic
     below changes!
  */
  value old;

  if (Is_young((value)fp)) {
    /* The modified object resides in the minor heap.
       Conditions 1 and 2 cannot occur. */
    *fp = val;
  } else {
    /* The modified object resides in the major heap. */
    CAMLassert(Is_in_heap(fp));
    old = *fp;
    *fp = val;
    if (Is_block(old)) {
      /* If [old] is a pointer within the minor heap, we already
         have a major->minor pointer and [fp] is already in the
         remembered set.  Conditions 1 and 2 cannot occur. */
      if (Is_young(old)) return;
      /* Here, [old] can be a pointer within the major heap.
         Check for condition 2. */
      if (caml_gc_phase == Phase_mark) caml_darken(old, NULL);
    }
    /* Check for condition 1. */
    if (Is_block(val) && Is_young(val)) {
      add_to_ref_table (Caml_state->ref_table, fp);
    }
  }
}


/* Global memory pool.

   The pool is structured as a ring of blocks, where each block's header
   contains two links: to the previous and to the next block. The data
   structure allows for insertions and removals of blocks in constant time,
   given that a pointer to the operated block is provided.

   Initially, the pool contains a single block -- a pivot with no data, the
   guaranteed existence of which makes for a more concise implementation.

   The API functions that operate on the pool receive not pointers to the
   block's header, but rather pointers to the block's "data" field. This
   behaviour is required to maintain compatibility with the interfaces of
   [malloc], [realloc], and [free] family of functions, as well as to hide
   the implementation from the user.
*/

/* A type with the most strict alignment requirements */
union max_align {
  char c;
  short s;
  long l;
  int i;
  float f;
  double d;
  void *v;
  void (*q)(void);
};

struct pool_block {
#ifdef DEBUG
  intnat magic;
#endif
  struct pool_block *next;
  struct pool_block *prev;
  /* Use C99's flexible array types if possible */
#if (__STDC_VERSION__ >= 199901L)
  union max_align data[];  /* not allocated, used for alignment purposes */
#else
  union max_align data[1];
#endif
};

#if (__STDC_VERSION__ >= 199901L)
#define SIZEOF_POOL_BLOCK sizeof(struct pool_block)
#else
#define SIZEOF_POOL_BLOCK offsetof(struct pool_block, data)
#endif

static struct pool_block *pool = NULL;


/* Returns a pointer to the block header, given a pointer to "data" */
static struct pool_block* get_pool_block(caml_stat_block b)
{
  if (b == NULL)
    return NULL;

  else {
    struct pool_block *pb =
      (struct pool_block*)(((char*)b) - SIZEOF_POOL_BLOCK);
#ifdef DEBUG
    CAMLassert(pb->magic == Debug_pool_magic);
#endif
    return pb;
  }
}

CAMLexport void caml_stat_create_pool(void)
{
  if (pool == NULL) {
    pool = malloc(SIZEOF_POOL_BLOCK);
    if (pool == NULL)
      caml_fatal_error("out of memory");
#ifdef DEBUG
    pool->magic = Debug_pool_magic;
#endif
    pool->next = pool;
    pool->prev = pool;
  }
}

CAMLexport void caml_stat_destroy_pool(void)
{
  if (pool != NULL) {
    pool->prev->next = NULL;
    while (pool != NULL) {
      struct pool_block *next = pool->next;
      free(pool);
      pool = next;
    }
    pool = NULL;
  }
}

/* [sz] and [modulo] are numbers of bytes */
CAMLexport void* caml_stat_alloc_aligned_noexc(asize_t sz, int modulo,
                                               caml_stat_block *b)
{
  char *raw_mem;
  uintnat aligned_mem;
  CAMLassert (0 <= modulo && modulo < Page_size);
  raw_mem = (char *) caml_stat_alloc_noexc(sz + Page_size);
  if (raw_mem == NULL) return NULL;
  *b = raw_mem;
  raw_mem += modulo;                /* Address to be aligned */
  aligned_mem = (((uintnat) raw_mem / Page_size + 1) * Page_size);
#ifdef DEBUG
  {
    uintnat *p;
    uintnat *p0 = (void *) *b;
    uintnat *p1 = (void *) (aligned_mem - modulo);
    uintnat *p2 = (void *) (aligned_mem - modulo + sz);
    uintnat *p3 = (void *) ((char *) *b + sz + Page_size);
    for (p = p0; p < p1; p++) *p = Debug_filler_align;
    for (p = p1; p < p2; p++) *p = Debug_uninit_align;
    for (p = p2; p < p3; p++) *p = Debug_filler_align;
  }
#endif
  return (char *) (aligned_mem - modulo);
}

/* [sz] and [modulo] are numbers of bytes */
CAMLexport void* caml_stat_alloc_aligned(asize_t sz, int modulo,
                                         caml_stat_block *b)
{
  void *result = caml_stat_alloc_aligned_noexc(sz, modulo, b);
  /* malloc() may return NULL if size is 0 */
  if ((result == NULL) && (sz != 0))
    caml_raise_out_of_memory();
  return result;
}

/* [sz] is a number of bytes */
CAMLexport caml_stat_block caml_stat_alloc_noexc(asize_t sz)
{
  /* Backward compatibility mode */
  if (pool == NULL)
    return malloc(sz);
  else {
    struct pool_block *pb = malloc(sz + SIZEOF_POOL_BLOCK);
    if (pb == NULL) return NULL;
#ifdef DEBUG
    memset(&(pb->data), Debug_uninit_stat, sz);
    pb->magic = Debug_pool_magic;
#endif

    /* Linking the block into the ring */
    pb->next = pool->next;
    pb->prev = pool;
    pool->next->prev = pb;
    pool->next = pb;

    return &(pb->data);
  }
}

/* [sz] is a number of bytes */
CAMLexport caml_stat_block caml_stat_alloc(asize_t sz)
{
  void *result = caml_stat_alloc_noexc(sz);
  /* malloc() may return NULL if size is 0 */
  if ((result == NULL) && (sz != 0))
    caml_raise_out_of_memory();
  return result;
}

CAMLexport void caml_stat_free(caml_stat_block b)
{
  /* Backward compatibility mode */
  if (pool == NULL)
    free(b);
  else {
    struct pool_block *pb = get_pool_block(b);
    if (pb == NULL) return;

    /* Unlinking the block from the ring */
    pb->prev->next = pb->next;
    pb->next->prev = pb->prev;

    free(pb);
  }
}

/* [sz] is a number of bytes */
CAMLexport caml_stat_block caml_stat_resize_noexc(caml_stat_block b, asize_t sz)
{
  if(b == NULL)
    return caml_stat_alloc_noexc(sz);
  /* Backward compatibility mode */
  if (pool == NULL)
    return realloc(b, sz);
  else {
    struct pool_block *pb = get_pool_block(b);
    struct pool_block *pb_new = realloc(pb, sz + SIZEOF_POOL_BLOCK);
    if (pb_new == NULL) return NULL;

    /* Relinking the new block into the ring in place of the old one */
    pb_new->prev->next = pb_new;
    pb_new->next->prev = pb_new;

    return &(pb_new->data);
  }
}

/* [sz] is a number of bytes */
CAMLexport caml_stat_block caml_stat_resize(caml_stat_block b, asize_t sz)
{
  void *result = caml_stat_resize_noexc(b, sz);
  if (result == NULL)
    caml_raise_out_of_memory();
  return result;
}

/* [sz] is a number of bytes */
CAMLexport caml_stat_block caml_stat_calloc_noexc(asize_t num, asize_t sz)
{
  uintnat total;
  if (caml_umul_overflow(sz, num, &total))
    return NULL;
  else {
    caml_stat_block result = caml_stat_alloc_noexc(total);
    if (result != NULL)
      memset(result, 0, total);
    return result;
  }
}

CAMLexport caml_stat_string caml_stat_strdup_noexc(const char *s)
{
  size_t slen = strlen(s);
  caml_stat_block result = caml_stat_alloc_noexc(slen + 1);
  if (result == NULL)
    return NULL;
  memcpy(result, s, slen + 1);
  return result;
}

CAMLexport caml_stat_string caml_stat_strdup(const char *s)
{
  caml_stat_string result = caml_stat_strdup_noexc(s);
  if (result == NULL)
    caml_raise_out_of_memory();
  return result;
}

#ifdef _WIN32

CAMLexport wchar_t * caml_stat_wcsdup(const wchar_t *s)
{
  int slen = wcslen(s);
  wchar_t* result = caml_stat_alloc((slen + 1)*sizeof(wchar_t));
  if (result == NULL)
    caml_raise_out_of_memory();
  memcpy(result, s, (slen + 1)*sizeof(wchar_t));
  return result;
}

#endif

CAMLexport caml_stat_string caml_stat_strconcat(int n, ...)
{
  va_list args;
  char *result, *p;
  size_t len = 0;
  int i;

  va_start(args, n);
  for (i = 0; i < n; i++) {
    const char *s = va_arg(args, const char*);
    len += strlen(s);
  }
  va_end(args);

  result = caml_stat_alloc(len + 1);

  va_start(args, n);
  p = result;
  for (i = 0; i < n; i++) {
    const char *s = va_arg(args, const char*);
    size_t l = strlen(s);
    memcpy(p, s, l);
    p += l;
  }
  va_end(args);

  *p = 0;
  return result;
}

#ifdef _WIN32

CAMLexport wchar_t* caml_stat_wcsconcat(int n, ...)
{
  va_list args;
  wchar_t *result, *p;
  size_t len = 0;
  int i;

  va_start(args, n);
  for (i = 0; i < n; i++) {
    const wchar_t *s = va_arg(args, const wchar_t*);
    len += wcslen(s);
  }
  va_end(args);

  result = caml_stat_alloc((len + 1)*sizeof(wchar_t));

  va_start(args, n);
  p = result;
  for (i = 0; i < n; i++) {
    const wchar_t *s = va_arg(args, const wchar_t*);
    size_t l = wcslen(s);
    memcpy(p, s, l*sizeof(wchar_t));
    p += l;
  }
  va_end(args);

  *p = 0;
  return result;
}

#endif
