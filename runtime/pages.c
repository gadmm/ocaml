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
#include "caml/platform.h"
#include "caml/skiplist.h"

// Mask for the hardcoded page size (fast), used for static data
#define Page_mask (~(Page_size - 1))

uintnat caml_use_huge_pages = 1;
/* True iff the program allocates heap chunks by mmapping huge pages.
   This is set when parsing [OCAMLRUNPARAM] and must stay constant
   after that.
*/

/* Reserving, committing, decommitting. Platform-independent. */


/* Round up to the nearest small page or huge page, depending on what
   is best. */
static asize_t round_up_to_huge_page(asize_t size)
{
  asize_t page_size = caml_use_huge_pages ? Huge_page_size : Real_page_size;
  return round_up(size, page_size);
}

// reserve at least [request] contiguous memory, rounded up to the
// Pagetable_entry_size and record it with the page table.
int caml_mem_reserve(asize_t request, int kind,
                     char **out_block, asize_t *out_reserved)
{
  char *mem;
  request = round_up(request, Pagetable_entry_size);
  /* hint at reserving near the previous block to
     have a good location in the page table. */
  mem = caml_mem_reserve_os(request, Pagetable_entry_size);
  if (mem == NULL) return -1;
  *out_block = mem;
  *out_reserved = request;
  /* keep reserved in case of error of the page table */
  return caml_page_table_add(kind, mem, mem + request);
}

/* [block] must be aligned to huge pages, and there must be enough
   reserved space to round the request up to the nearest page or huge
   page. If successful, [out_size] is set to the size that was
   actually committed. In case of error the whole range is
   now invalid. */
int caml_mem_commit(char *block, asize_t request, asize_t *out_size)
{
  request = round_up_to_huge_page(request);
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

/* TODO: move to a separate file */
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
    if (-1 == caml_mem_reserve(request, In_heap, &mem, &new_reserve))
      return -1;
    pa_merge(&heap_allocator, mem, new_reserve);
    // Now it should succeed
    pa_alloc(&heap_allocator, request, &block, &reserved) ?: CAMLassert(0);
  }
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
}
