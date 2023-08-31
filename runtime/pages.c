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
#include <stdatomic.h>
#include <unistd.h>
#include <sys/mman.h>
#include "caml/address_class.h"
#include "caml/pages.h"
#include "caml/skiplist.h"

uintnat caml_use_huge_pages = 1;
/* True iff the program allocates heap chunks by mmapping huge pages.
   This is set when parsing [OCAMLRUNPARAM] and must stay constant
   after that.
*/

/* Page table management */

atomic_char *caml_heap_table = NULL;
uintnat caml_real_page_size = 0;

#ifdef ARCH_SIXTYFOUR

/* Number of significant bits for pointers in the heap. Determines
   reserved (not committed) area for page table; can support 57 bits
   etc. */
#define Pagetable_significant_bits 48

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

#define Pagetable_significant_bits 32
#define Pagetable_initial_bits 32

#endif /* ARCH_SIXTYFOUR */

#define Pagetable_log (Pagetable_significant_bits - Pagetable_entry_log)
#define Pagetable_size (((int)1 << Pagetable_log))
#define Pagetable_initial_size                                  \
  (((int)1 << (Pagetable_initial_bits - Pagetable_entry_log)))

static_assert(Pagetable_log < 8 * sizeof(int), "invalid page sizes");

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

#define CAMLassert_aligned_(n, m)                     \
  (CAMLassert(((uintnat)n & ((uintnat)m - 1)) == 0))
#define CAMLassert_aligned(n, m)                          \
  (CAMLassert_is_power_of_2(m),CAMLassert_aligned_(n,m))
#define CAMLassert_is_power_of_2(n) CAMLassert_aligned_(n, n)

static intnat round_down(intnat n, intnat mod)
{
  return mod * (n / mod  - (n < 0 ? 1 : 0));
}

static intnat round_up(intnat n, intnat mod)
{
  return round_down(n + mod - 1, mod);
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
      //   the same virtual space can later be acquired by the runtime.
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


/* Round up to the nearest small page or huge page, depending on what
   is best. */
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
  /* size of pages managed, typically Huge_page_log or Page_log */
  int const page_log;
  /* address of each allocated block and its size */
  struct skiplist free_per_address_sk;
  /* each allocated block ordered per decreasing size.

     key: lexicographic ordering by size (decreasing) and address.

       ~( # huge pages )      msbs of address
     |-------------------|------------------------|
        num_max_log bits   small_address_log bits
  */
  struct skiplist free_per_size_sk;
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
  return caml_skiplist_find(&pa->free_per_address_sk,
                            (uintnat)block, (uintnat *)size_out);
}

Caml_inline int pa_find_below_address(page_allocator *pa, char *addr,
                                      char **block_out, asize_t *size_out)
{
  uintnat address;
  if (caml_skiplist_find_below(&pa->free_per_address_sk, (uintnat)addr,
                               &address, (uintnat *)size_out)) {
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
                              pa_size_key(pa, beg, size), (uintnat *)&size)
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
