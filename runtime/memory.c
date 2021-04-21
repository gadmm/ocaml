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

#include <stdlib.h>
#include <string.h>
#include <stdarg.h>
#include <stddef.h>
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

int caml_huge_fallback_count = 0;
/* Number of times that mmapping big pages fails and we fell back to small
   pages. This counter is available to the program through
   [Gc.huge_fallback_count].
*/

uintnat caml_use_huge_pages = 0;
/* True iff the program allocates heap chunks by mmapping huge pages.
   This is set when parsing [OCAMLRUNPARAM] and must stay constant
   after that.
*/

extern uintnat caml_percent_free;                   /* major_gc.c */

/* Page table management */

uintnat *caml_heap_table;
static struct skiplist static_area_sk = SKIPLIST_STATIC_INITIALIZER;

#define Pagetable_log (Pagetable_significant_bits - Pagetable_page_log) // 20
#define Pagetable_size (((uintnat)1 << Pagetable_log) / Pages_per_entry)

int caml_is_in_value_area(void *addr)
{
  uintnat data;
  if (Is_in_heap_or_young(addr)) return 1;
  return caml_skiplist_find(&static_area_sk, (uintnat)addr & Page_mask, &data);
}

static void static_area_insert(void * start, void * end)
{
  uintnat pstart = (uintnat) start & Page_mask;
  uintnat pend = ((uintnat) end - 1) & Page_mask;
  uintnat p;
  // Lots of optimisation opportunities (just record the beginning and
  // end of the whole segment, record ranges of pages...)
  for (p = pstart; p <= pend; p += Page_size)
    caml_skiplist_insert(&static_area_sk, p, 0);
}

int caml_page_table_initialize(mlsize_t bytesize)
{
  // 2^(Pagetable_log - Page_log - 3) = 32 pages that are
  // zero-initialised and mapped to the zero page until modified
  // (Linux).
  void *block = mmap(NULL, Pagetable_size * sizeof(uintnat),
                     PROT_READ | PROT_WRITE,
                     MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  if (block == MAP_FAILED) return -1;
  caml_heap_table = (uintnat *)block;
  return 0;
  // todo: free on shutdown
}

static void set_bit(uintnat p)
{
  caml_heap_table[p / Pages_per_entry] |=
    (((uintnat)1) << (p % Pages_per_entry));
}

static void clear_bit(uintnat p)
{
  caml_heap_table[p / Pages_per_entry] &=
    ~(((uintnat)1) << (p % Pages_per_entry));
}

static int page_table_modify_range(int val, void * start, void * end)
{
  uintnat pstart = Large_page(start);
  uintnat pend = Large_page((uintnat)end - 1);
  uintnat p;

  for (p = pstart; p <= pend; p++) {
    if (val) set_bit(p);
    else clear_bit(p);
  }
  return 0;
}

int caml_page_table_add(int kind, void * start, void * end)
{
  if (kind == In_heap)
    page_table_modify_range(1, start, end);
  if (kind == In_static_data)
    static_area_insert(start, end);
  return 0;
}

int caml_page_table_remove(int kind, void * start, void * end)
{
  CAMLassert(kind != In_static_data);
  page_table_modify_range(0, start, end);
  return 0;
}

static uintnat round_up(uintnat n, uintnat mod)
{
  return (n + mod - 1) / mod * mod;
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
  static void *last_block = NULL;
  char *mem;
  asize_t request_virtual;
  char *block;
  if (caml_use_huge_pages){
#ifndef HAS_HUGE_PAGES
    return NULL;
#else
    uintnat size = round_up(request + sizeof(heap_chunk_head), Heap_page_size);
    CAMLassert(Heap_page_size >= Pagetable_page_size); // TODO: always false
    block = mmap (NULL, size, PROT_READ | PROT_WRITE,
                  MAP_PRIVATE | MAP_ANONYMOUS | MAP_HUGETLB, -1, 0);
    if (block == MAP_FAILED) return NULL;
    mem = block + sizeof (heap_chunk_head);
    CAMLassert( ((uintnat) block & (Heap_page_size - 1)) == 0 );
    Chunk_size (mem) = size - sizeof (heap_chunk_head);
    Chunk_block (mem) = block;
#endif
  }else{
    asize_t reserve;
    // todo: free on shutdown
    // todo: have a better test for THP availability
#ifdef HAS_HUGE_PAGES
    int huge_pages = 1;//request > (Heap_page_size / 2);
#else
    int huge_pages = 0;
#endif
    uintnat page_size = huge_pages ? Heap_page_size : Page_size;
    request = request + sizeof(heap_chunk_head);
    request = round_up(request, page_size);
    reserve = round_up(request, Pagetable_page_size);
    request_virtual = reserve + Pagetable_page_size;
    /* hint at reserving near the previous block to
       have a good location in the page table. */
    block = mmap(last_block, request_virtual, PROT_NONE,
                 MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (block == MAP_FAILED) return NULL;
    mem = (char *) round_up((uintnat) block, Pagetable_page_size);
    CAMLassert((uintnat) mem + reserve <= (uintnat) block + request_virtual);
    /* free beginning */
    munmap(block, mem - block);
    /* free end */
    munmap(mem + reserve, request_virtual - (mem - block) - reserve);
    /* [mem..mem+reserve[ is reserved */
#ifdef HAS_HUGE_PAGES
    /* Request huge pages (THP), always. Note: this can cause large
       pauses if /sys/kernel/mm/transparent_hugepage/defrag is set to
       [always] or [madvise]. However, benefits are already observed
       without this call.
       TODO: Either one can let the user be responsible for their
       defrag setting (at risk of breaking workflows), or one can
       repurpose the H option for doing the call below. */
    if (huge_pages) {
      if (madvise(mem, request, MADV_HUGEPAGE) == -1) goto err;
    }
#endif
    /* Commit [mem..mem+request[ */
    if (mprotect(mem, request, PROT_READ | PROT_WRITE) == -1) goto err;
    block = mem;
    mem += sizeof(heap_chunk_head);
    Chunk_size(mem) = request - sizeof(heap_chunk_head);
    Chunk_block(mem) = block;
    Chunk_block_size(mem) = reserve;
    last_block = block;
  }
  Chunk_head (mem)->redarken_first.start = (value*)(mem + Chunk_size(mem));
  Chunk_head (mem)->redarken_first.end = (value*)(mem + Chunk_size(mem));
  Chunk_head (mem)->redarken_end = (value*)mem;
  return mem;
 err:
  munmap(block, request_virtual);
  return NULL;
}

/* Same as caml_alloc_for_heap, but avoids e.g. serving a 4MB block in
   response to a 2MB request. Instead, serve a block slightly smaller
   than requested. */
char *caml_alloc_for_minor_heap(asize_t request)
{
  return caml_alloc_for_heap(request - sizeof(heap_chunk_head));
}

/* Use this function to free a block allocated with
   [caml_alloc_for_heap] or [caml_alloc_for_minor_heap] if you don't
   add it with [caml_add_to_heap].
*/
void caml_free_for_heap (char *mem)
{
  if (caml_use_huge_pages){
#ifdef HAS_HUGE_PAGES
    munmap (Chunk_block (mem), Chunk_size (mem) + sizeof (heap_chunk_head));
#else
    CAMLassert (0);
#endif
  }else{
    munmap(Chunk_block(mem), Chunk_block_size(mem));
  }
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

  /* Remove the pages of [chunk] from the page table. */
  caml_page_table_remove(In_heap, chunk, chunk + Chunk_size (chunk));

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
