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
#include <unistd.h>
#include <sys/mman.h>
#include "caml/pages.h"
#include "caml/platform.h"
#include "caml/skiplist.h"

uintnat caml_real_page_size = 0;

/* Reservation, platform-specific */

static void mem_unmap_os(char *block, asize_t size)
{
  if (size != 0) {
    int ret = munmap(block, size);
    CAMLassert(ret != -1 || errno != EINVAL);
    (void)ret;
  }
}

static struct skiplist mmaped_areas = SKIPLIST_STATIC_INITIALIZER;

void caml_mem_unreserve_all(void)
{
  FOREACH_SKIPLIST_ELEMENT(elem, &mmaped_areas, {
      mem_unmap_os((char *)elem->key, (asize_t)elem->data);
    });
}

/* Reserve [size] bytes, aligned at [align]. [size] must be a multiple
   of [align] and align a power of 2. */
char * caml_mem_reserve_os(asize_t size, asize_t align)
{
  // All platforms except win32. TODO: see golang for win32.
  static char *last_mem = NULL;
  static asize_t last_size = 0;
  char *mem;
  char *block;
  asize_t request_virtual = size + align;
  CAMLassert_is_power_of_2(align);
  CAMLassert_aligned(size, align);
  // Hint at the end of the previously-reserved block
  block = mmap(last_mem + last_size, request_virtual, PROT_NONE,
               MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  if (block == MAP_FAILED) return NULL;
  // Prefer contiguous if possible, to avoid holes in the VAS
  if (block + request_virtual == last_mem) {
    // This is likely to happen on Linux, where the mmaped area grows
    // downwards
    mem = last_mem - size;
  } else {
    mem = (char *) round_up((uintnat)block, align);
  }
  CAMLassert((uintnat) mem + size <= (uintnat) block + request_virtual);
  /* free beginning */
  mem_unmap_os(block, mem - block);
  /* free end */
  mem_unmap_os(mem + size, request_virtual - (mem - block) - size);
  /* [mem..mem+size[ is reserved */
  caml_skiplist_insert(&mmaped_areas, (uintnat)mem, (uintnat)size);
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

// can be used to recommit (preserves already-committed mapping)
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
