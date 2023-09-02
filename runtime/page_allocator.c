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
#include "caml/address_class.h"
#include "caml/page_allocator.h"
#include "caml/platform.h"
#include "caml/skiplist.h"

#define PA_page_size(pa) ((uintnat)1 << (pa)->page_log)
#define PA_small_address_log(pa) (Pagetable_significant_bits - (pa)->page_log)
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

int caml_pa_find_below_address(page_allocator *pa, char *addr,
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

void caml_pa_merge(page_allocator *pa, char *block, asize_t size)
{
  char *block_before;
  char *block_after = block + size;
  asize_t size_before, size_after;
  /* Merge with block before */
  if (caml_pa_find_below_address(pa, block, &block_before, &size_before)) {
    if (block_before + size_before == block
        && size + size_before <= PA_size_max(pa)) {
      pa_remove_free(pa, block_before, size_before);
      block = block_before;
      size += size_before;
    }
  }
  /* Merge with block after */
  if (pa_find_address(pa, block_after, &size_after)
      && size + size_after <= PA_size_max(pa)) {
    pa_remove_free(pa, block_after, size_after);
    size += size_after;
  }
  pa_add_free(pa, block, size);
}

int caml_pa_alloc(page_allocator *pa, asize_t request,
                  char **block_out, asize_t *size_out)
{
  char *block;
  asize_t available;
  request = round_up(request, PA_page_size(pa));
  if (pa_find_above_size(pa, request, &block, &available)) {
    char *new_block;
    pa_remove_free(pa, block, available);
    if (MMAP_GROWS_DOWN) {
      /* Commit the end to avoid holes, later, in the committed VAS,
         on platforms where mmap grows down */
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

void caml_pa_print(page_allocator *pa)
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
