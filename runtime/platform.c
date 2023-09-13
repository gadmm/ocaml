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
#include <stdbool.h>
#include "caml/pages.h"
#include "caml/platform.h"
#include "caml/skiplist.h"

#ifdef __linux__
#include <fcntl.h>
#endif

#ifdef __FreeBSD__
#include <sys/sysctl.h>
#endif

#ifdef _WIN32
#include <windows.h>
#else
#include <sys/mman.h>
#endif

uintnat caml_real_page_size = Page_size;
static bool caml_os_overcommit = false;

/* The following function is from mimalloc.
   Copyright (c) 2018-2023, Microsoft Research, Daan Leijen
   You can redistribute it and/or modify it under the terms of the MIT license.
*/

static bool unix_detect_overcommit(void) {
  bool os_overcommit = true;
#if defined(__linux__)
  int fd = open("/proc/sys/vm/overcommit_memory", O_RDONLY);
  if (fd >= 0) {
    char buf[32];
    ssize_t nread = read(fd, &buf, sizeof(buf));
    close(fd);
    // <https://www.kernel.org/doc/Documentation/vm/overcommit-accounting>
    // 0: heuristic overcommit, 1: always overcommit,
    // 2: never overcommit (ignore NORESERVE)
    if (nread >= 1) {
      os_overcommit = (buf[0] == '0' || buf[0] == '1');
    }
  }
#elif defined(__FreeBSD__)
  int val = 0;
  size_t olen = sizeof(val);
  if (sysctlbyname("vm.overcommit", &val, &olen, NULL, 0) == 0) {
    os_overcommit = (val != 0);
  }
#elif defined(__APPLE__)
  os_overcommit = false;
#else
  // default: overcommit is true
#endif
  return os_overcommit;
}

/* End of MIT license. */

void caml_mem_os_init(void)
{
#ifndef _WIN32
  caml_real_page_size = sysconf(_SC_PAGESIZE);
  CAMLassert(caml_real_page_size >= Page_size);
  caml_os_overcommit = unix_detect_overcommit();
#endif
}

/* Reserving & committing memory, platform-specific */

static void mem_unmap_os(char *block, asize_t size);

static char * mem_reserve_os(asize_t size, asize_t align)
{
  char *mem;
  char *block;
  asize_t request_virtual;
  bool failed;
#ifndef _WIN32
  static char *last_mem = NULL;
  static asize_t last_size = 0;
#else // _WIN32
  int tries = 1000;
#endif
  /* The minimum alignment is to the page size, in which case it is
     obtained for free */
  if (align <= Real_page_size) align = 0;
  request_virtual = size + align;
#ifndef _WIN32
  /* Hint at the end of the previously-reserved block */
  block = mmap(last_mem + last_size, request_virtual, PROT_NONE,
               MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  failed = (block == MAP_FAILED);
#else // _WIN32
again:
  block = VirtualAlloc(NULL, request_virtual, MEM_RESERVE, PAGE_NOACCESS);
  failed = (block == NULL);
#endif
  if (failed) return NULL;
  if (align == 0) {
    mem = block;
    goto done;
  }
  /* Trim to an aligned region */
  /* Prefer contiguous if possible, to avoid holes in the VAS */
  if (block + request_virtual == last_mem || MMAP_GROWS_DOWN) {
    /* This case is likely to happen on Linux, where the mmaped area grows
       downwards */
    mem = (char *) Round_down((uintnat)block + request_virtual - size, align);
  } else {
    mem = (char *) Round_up((uintnat)block, align);
  }
  CAMLassert((uintnat) mem >= (uintnat) block);
  CAMLassert((uintnat) mem + size <= (uintnat) block + request_virtual);
#ifndef _WIN32
  /* free beginning */
  mem_unmap_os(block, mem - block);
  /* free end */
  mem_unmap_os(mem + size, request_virtual - (mem - block) - size);
 done:
  /* [mem..mem+size[ is reserved */
  last_mem = mem;
  last_size = size;
#else // _WIN32
  /* VirtualFree can be used to decommit portions of memory, but it
     can only release the entire block of memory. For Windows, repeat
     the call but this time specify the address. This is racy, so it
     might fail, in which case we retry. */
  VirtualFree(block, 0, MEM_RELEASE);
  block = VirtualAlloc((void*)mem, size, MEM_RESERVE, PAGE_NOACCESS);
  if (block == NULL) {
    /* VirtualAlloc can return the following three interesting errors:
         - ERROR_INVALID_ADDRESS - pages are already reserved (race)
         - ERROR_NOT_ENOUGH_MEMORY - address space exhausted
         - ERROR_COMMITMENT_LIMIT - memory exhausted */
    if (GetLastError() == ERROR_INVALID_ADDRESS && tries-- > 0) {
      SetLastError(0);
      /* Raced - try again. */
      goto again;
    } else {
      return NULL;
    }
  }
 done:
#endif
  return mem;
}

#ifndef _WIN32

static int madvise_os(char *block, asize_t size, int madvice)
{
  int err;
  /* EAGAIN is Linux-specific */
  while (-1 == (err = madvise(block, size, madvice)) && errno == EAGAIN) {};
  return err;
}

/* Adjust alignment to page for mprotect/madvise */
static void adjust_to_page(char **block, asize_t *size)
{
  uintnat start = (uintnat)*block;
  uintnat start_aligned = Round_down(start, Real_page_size);
  uintnat size_aligned =
    Round_up(*size + (start - start_aligned), Real_page_size);
  *size = size_aligned;
  *block = (char *)start_aligned;
}

#endif

static int mem_commit_os(char *block, asize_t size)
{
#ifndef _WIN32
  /* - Commit:
        - MADV_FREE_REUSE on Darwin
        - MADV_DODUMP, MADV_CORE. Darwin: none.
     Can we ensure it fails on OOM if overcommitting is off? */
  adjust_to_page(&block, &size);
  if (-1 == mprotect(block, size, PROT_READ | PROT_WRITE)) return -1;
#if defined(MADV_DODUMP)
  /* cancel MADV_DONTDUMP (Linux) */
  madvise_os(block, size, MADV_DODUMP); // ignore error
#elif defined(MADV_CORE)
  /* cancel MADV_NOCORE (FreeBSD) */
  madvise_os(block, size, MADV_CORE); // ignore error
#endif
#ifdef MADV_FREE_REUSE
  /* cancel MADV_FREE_REUSABLE (Darwin). Calling
     madvise(MADV_FREE_REUSE) has no effect on areas where
     madvise(MADV_FREE_REUSABLE) was not called. */
  madvise_os(block, size, MADV_FREE_REUSE); // ignore error
#endif
#ifdef MADV_HUGEPAGE // Linux
  if (caml_use_huge_pages
      && (uintnat)block == Round_down((uintnat)block, Huge_page_size)
      && (uintnat)size == Round_down((uintnat)size, Huge_page_size)) {
    /* Request huge pages (THP) if huge pages are enabled and the
       region is Huge-page-aligned. Note: this can cause large pauses
       if /sys/kernel/mm/transparent_hugepage/defrag is set to
       [always], [madvise] or [defer+madvise], since OCaml will try to
       touch a lot of huge pages at once. [defer] is preferred. */
    madvise_os(block, size, MADV_HUGEPAGE); // ignore error
    /* TODO: restore hugetlb behaviour for backwards-compat. */
  }
#endif
  return 0;
#else // _WIN32
  void *m = VirtualAlloc((void*)block, size, MEM_COMMIT, PAGE_READWRITE);
  bool ret == (!!m - 1);
  if (ret == -1) {
    if (GetLastError() == ERROR_NOT_ENOUGH_MEMORY
        || GetLastError() == ERROR_COMMITMENT_LIMIT)
      errno = ENOMEM;
    else
      errno = EINVAL;
  }
  return (!!ret) - 1;
#endif
}

static void mem_decommit_os(char * block, asize_t size)
{
#ifndef _WIN32
  /* - Decommit:
        - MADV_DONTNEED on Linux with overcommitting
          cf. https://github.com/golang/go/issues/42330
        - MADV_FREE on BSD
          and Haiku, MADV_FREE_REUSABLE on Darwin, MADV_DONTNEED as a
          fallback, posix_madvise & POSIX_MADV_DONTNEED as a fallback?
        - mmap(PROT_NONE,MAP_FIXED) to decommit in Linux without
          overcommitting (see jemalloc,glibc malloc)
          (https://github.com/bminor/glibc/commit/9fab36eb58)
        - MADV_FREE exists on Linux, so be careful about #ifdef.
          MADV_FREE is more lazy in reclaiming memory, so we prefer
          MADV_DONTNEED here since we decommit when we really want to free
          memory.
        - MADV_DONTDUMP on Linux, MADV_NOCORE on BSD. (Not needed for
          core files, but seems to help gdb) Darwin: NONE  */
  int advice;
  adjust_to_page(&block, &size);
#if defined(__linux__)
  if (!caml_os_overcommit) {
    mmap(block, size, PROT_NONE, MAP_FIXED | MAP_PRIVATE | MAP_ANONYMOUS,
         -1, 0);
    return;
  }
#endif
#if defined(MADV_FREE_REUSABLE) // Darwin
  advice = MADV_FREE_REUSABLE;
#elif (defined(MADV_FREE) && !defined(__linux__))
  advice = MADV_FREE;
#else
  advice = MADV_DONTNEED;
#endif
  /* ignore errors */
  madvise_os(block, size, advice);
#if defined(MADV_DONTDUMP) // Linux
  madvise_os(block, size, MADV_DONTDUMP);
#elif defined(MADV_NOCORE) // FreeBSD
  madvise_os(block, size, MADV_NOCORE);
#endif
#else // _WIN32
  VirtualFree((void *)block, size, MEM_DECOMMIT);
#endif
}

/* Only accepts full reserved areas */
static void mem_unmap_os(char *block, asize_t size)
{
  bool failed;
  if (size == 0) return;
#ifndef _WIN32
  failed = (munmap(block, size) == -1);
  CAMLassert(!failed || errno != EINVAL);
#else // _WIN32
  failed = !VirtualFree(mem, 0, MEM_RELEASE);
#endif
  if (failed) {
    caml_gc_message(0x1000, "decommit %zu bytes at %p failed\n", size, block);
  };
}

/* Wrapped functions */

static struct skiplist mmaped_areas = SKIPLIST_STATIC_INITIALIZER;

void caml_mem_unreserve_all(void)
{
  FOREACH_SKIPLIST_ELEMENT(elem, &mmaped_areas, {
      char *block = (char *)elem->key;
      asize_t size = (asize_t)elem->data;
      caml_gc_message(0x1000, "decommit %zu bytes at %p for heaps\n",
                      size, block);
      mem_unmap_os(block, size);
    });
}

/* Reserve [size] bytes, aligned at [align]. [size] must be a multiple
   of [align] and align a power of 2. */
char * caml_mem_reserve_os(asize_t size, asize_t align)
{
  char *mem;
  CAMLassert_is_power_of_2(align);
  CAMLassert_aligned(size, align);
  mem = mem_reserve_os(size, align);
  if (mem == NULL) {
    caml_gc_message(0x1000, "reserving %zu bytes with alignment %zu failed\n",
                    size, align);
    return NULL;
  }
  CAMLassert_aligned(mem, align);
  caml_gc_message(0x1000, "reserved %zu bytes with alignment %zu "
                          "at %p for heaps\n", size, align, mem);
  /* remember the mmaped area for cleanup at exit */
  caml_skiplist_insert(&mmaped_areas, (uintnat)mem, (uintnat)size);
  return mem;
}

/* can be used to recommit (preserves already-committed mapping) */
int caml_mem_commit_os(char *block, asize_t size)
{
  caml_gc_message(0x1000, "committing %zu bytes at %p for heaps\n",
                  size, block);
  return mem_commit_os(block, size);
}

void caml_mem_decommit_os(char * block, asize_t size)
{
  if (size == 0) return;
  caml_gc_message(0x1000, "decommitting %zu bytes at %p for heaps\n",
                  size, block);
  mem_decommit_os(block, size);
}
