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
#include <stdbool.h>
#include <string.h>
#include "caml/platform.h"
#include "caml/skiplist.h"

#ifdef HAS_UNISTD
#include <unistd.h>
#endif

#ifdef _WIN32
#include <windows.h>
#else
#include <sys/mman.h>
#endif

/* True iff the program wants to allocate heap chunks by mmapping huge
   pages. This is set when parsing [OCAMLRUNPARAM] and must stay
   constant after that.
*/
uintnat caml_use_huge_pages = 1;

uintnat caml_real_page_size = Page_size;
static bool caml_os_overcommit = false;

/* The following function unix_detect_overcommit is from mimalloc.
   Copyright (c) 2018-2023, Microsoft Research, Daan Leijen
   You can redistribute it and/or modify it under the terms of the MIT license.
*/

#ifdef __linux__
#include <fcntl.h>
#endif

#ifdef __FreeBSD__
#include <sys/sysctl.h>
#endif

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

#ifndef _WIN32

#define UNDEFINED -1

#ifndef MADV_HUGEPAGE
#define MADV_HUGEPAGE UNDEFINED
#endif

#ifndef MADV_DODUMP
#define MADV_DODUMP UNDEFINED
#endif

#ifndef MADV_DONTDUMP
#define MADV_DONTDUMP UNDEFINED
#endif

#ifndef MADV_CORE
#define MADV_CORE UNDEFINED
#endif

#ifndef MADV_NOCORE
#define MADV_NOCORE UNDEFINED
#endif

#ifndef MADV_FREE
#define MADV_FREE UNDEFINED
#endif

#ifndef MADV_FREE_REUSE
#define MADV_FREE_REUSE UNDEFINED
#endif

#ifndef MADV_FREE_REUSABLE
#define MADV_FREE_REUSABLE UNDEFINED
#endif

#ifndef MADV_POPULATE_WRITE
#define MADV_POPULATE_WRITE UNDEFINED
#endif

static int madvise_os(char *block, asize_t size, int madvice)
{
  int err;
  CAMLassert(madvice != UNDEFINED);
  err = madvise(block, size, madvice);
  /* Note: there is no evidence that one should retry on EAGAIN */
  if (err == -1) {
    char * str = "(unknown)";
    /* There is no simpler way to convert to a string, but the message
       is useful as there is no other way to know that an error
       happens in the cases where our result is ignored. */
    if (madvice == MADV_DODUMP) str = "MADV_DODUMP";
    if (madvice == MADV_CORE) str = "MADV_CORE";
    if (madvice == MADV_FREE) str = "MADV_FREE";
    if (madvice == MADV_DONTNEED) str = "MADV_DONTNEED";
    if (madvice == MADV_FREE_REUSE) str = "MADV_FREE_REUSE";
    if (madvice == MADV_FREE_REUSABLE) str = "MADV_FREE_REUSABLE";
    if (madvice == MADV_HUGEPAGE) str = "MADV_HUGEPAGE";
    if (madvice == MADV_DONTDUMP) str = "MADV_DONTDUMP";
    if (madvice == MADV_NOCORE) str = "MADV_NOCORE";
    if (madvice == MADV_POPULATE_WRITE) str = "MADV_POPULATE_WRITE";
    if (madvice == UNDEFINED) str = "-1";
    caml_gc_message(0x1000,
                    "madvise failed (block=%p, "
                    "size=%" ARCH_SIZET_PRINTF_FORMAT "u, advice=%s) "
                    "with error: %s\n",
                    block, size, str, strerror(errno));
  }
  return err;
}

/* enable/cancel MADV_DONTDUMP (Linux) / MADV_NOCORE (FreeBSD), ignore
   errors. */
static void madvise_dodump(char *block, asize_t size, bool dodump)
{
  int madvice = UNDEFINED;
  if (MADV_DODUMP != UNDEFINED) madvice = dodump ? MADV_DODUMP : MADV_DONTDUMP;
  else if (MADV_CORE != UNDEFINED) madvice = dodump ? MADV_CORE : MADV_NOCORE;
  if (madvice != UNDEFINED) madvise_os(block, size, madvice);
}

#endif

static void mem_unmap_os(char *block, asize_t size);

static char * mem_reserve_os(asize_t size, asize_t align)
{
  char *mem;
  char *block;
  asize_t request_virtual;
  bool contiguous = false;
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
  if (block == MAP_FAILED) goto err;
  contiguous = (block + request_virtual == last_mem);
#else // _WIN32
 again:
  block = VirtualAlloc(NULL, request_virtual, MEM_RESERVE, PAGE_NOACCESS);
  if (block == NULL) goto err;
#endif
  if (align == 0) {
    mem = block;
    goto done;
  }
  /* Trim to an aligned region */
  /* Prefer contiguous if possible, to avoid holes in the VAS */
  if (contiguous || MMAP_GROWS_DOWN) {
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
  madvise_dodump(mem, size, false);
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
      goto err;
    }
  }
 done:
#endif
  return mem;
 err:
  caml_gc_message(0x1000,
                  "failed to reserve aligned memory "
                  "(%" ARCH_SIZET_PRINTF_FORMAT "u bytes aligned "
                  "at %" ARCH_SIZET_PRINTF_FORMAT "u)\n",
                  size, align);
  return NULL;
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

static bool mem_commit_os(char *block, asize_t size)
{
#ifndef _WIN32
  /* - Commit:
        - MADV_FREE_REUSE on Darwin
        - MADV_DODUMP, MADV_CORE. Darwin: none.
     Try to ensure it fails on OOM. */
  adjust_to_page(&block, &size);
  /* Huge pages on Linux */
  if (MADV_HUGEPAGE != UNDEFINED
      && caml_use_huge_pages
      && Is_aligned(block, Huge_page_size)
      && Is_aligned(size, Huge_page_size)) {
    /* Request huge pages (THP) if huge pages are enabled and the
       region is Huge-page-aligned. Note: this can cause large pauses
       if /sys/kernel/mm/transparent_hugepage/defrag is set to
       [always], [madvise] or [defer+madvise], since OCaml will try to
       touch a lot of huge pages at once. [defer] is preferred. */
    if (-1 == madvise_os(block, size, MADV_HUGEPAGE) && errno == EINVAL) {
      caml_gc_message(0x1000, "madvise(MADV_HUGEPAGE) failed with EINVAL, "
                              "disabling huge pages henceforth\n");
      caml_use_huge_pages = 0;
    } /* otherwise ignore error */
  }
  if (-1 == mprotect(block, size, PROT_READ | PROT_WRITE)) goto err;
  madvise_dodump(block, size, true);
  /* Darwin */
  if (MADV_FREE_REUSE != UNDEFINED) {
    /* cancel MADV_FREE_REUSABLE. Calling madvise(MADV_FREE_REUSE) has
       no effect on areas where madvise(MADV_FREE_REUSABLE) was not
       called. */
    if (-1 == madvise_os(block, size, MADV_FREE_REUSE)) {
      caml_gc_message(0x1000, "out of memory (failed to reuse mapping)");
      return false;
    }
  }
  /* Linux */
  if (MADV_POPULATE_WRITE != UNDEFINED && DO_POPULATE && caml_os_overcommit) {
    /* Populate all pages at once, and guarantee no SIGBUS with
       overcommitting. */
    if (-1 == madvise_os(block, size, MADV_POPULATE_WRITE)) {
      caml_gc_message(0x1000, "out of memory (failed to populate mapping)");
      return false;
    }
  }
#else // _WIN32
  void *m = VirtualAlloc((void*)block, size, MEM_COMMIT, PAGE_READWRITE);
  if (m == NULL) {
    bool oom =
      GetLastError() == ERROR_NOT_ENOUGH_MEMORY
      || GetLastError() == ERROR_COMMITMENT_LIMIT;
    errno = oom ? ENOMEM : EINVAL;
    goto err;
  }
#endif
  return true;
 err:
  caml_gc_message(0x1000,
                  "failed to commit mapping "
                  "(block=%p, size=%" ARCH_SIZET_PRINTF_FORMAT "u), "
                  "error=%s\n",
                  block, size, strerror(errno));
  return false;
}

static void mem_decommit_os(char * block, asize_t size)
{
#ifndef _WIN32
  /* - Decommit:
        - MADV_DONTNEED on Linux with overcommitting
          cf. https://github.com/golang/go/issues/42330
        - MADV_FREE on BSD (except FreeBSD without overcommitting)
          and Haiku, MADV_FREE_REUSABLE on Darwin, MADV_DONTNEED as a
          fallback, posix_madvise & POSIX_MADV_DONTNEED as a fallback?
        - mmap(PROT_NONE,MAP_FIXED) to decommit in Linux without
          overcommitting (see glibc malloc:
          https://github.com/bminor/glibc/commit/9fab36eb58). We
          assume we have to do something similar for FreeBSD without
          overcommitting.
        - MADV_FREE exists on Linux, so be careful about #ifdef.
          MADV_FREE is more lazy in reclaiming memory, so we prefer
          MADV_DONTNEED here since we decommit when we really want to free
          memory. (see e.g. Go, mimalloc)
        - MADV_DONTDUMP on Linux, MADV_NOCORE on BSD. (Not needed for
          core files, but seems to help gdb) Darwin: NONE  */
  int advice;
  adjust_to_page(&block, &size);
#if defined(__linux__) || defined(__FreeBSD__)
  if (!caml_os_overcommit) {
    void *res = mmap(block, size, PROT_NONE,
                     MAP_FIXED | MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (res == MAP_FAILED) {
      CAMLassert(errno != EINVAL);
      goto err;
    }
    return;
  }
#endif
  if (MADV_FREE_REUSABLE != UNDEFINED) advice = MADV_FREE_REUSABLE; /* Darwin */
#ifndef __linux__
  else if (MADV_FREE != UNDEFINED) advice = MADV_FREE; /* BSDs */
#endif
  else advice = MADV_DONTNEED; /* Linux and fallback */
  if (-1 == madvise_os(block, size, advice)) {
    CAMLassert(errno != EINVAL);
    goto err;
  }
  madvise_dodump(block, size, false);
#else // _WIN32
  if (!VirtualFree((void *)block, size, MEM_DECOMMIT)) goto err;
#endif
 err:
  caml_gc_message(0x1000, "decommitting %" ARCH_SIZET_PRINTF_FORMAT "u bytes"
                  " at %p failed\n", size, block);

}

/* Only accepts full reserved areas */
static void mem_unmap_os(char *block, asize_t size)
{
  if (size == 0) return;
#ifndef _WIN32
  if (munmap(block, size) == -1) {
    CAMLassert(errno != EINVAL);
    goto err;
  }
#else // _WIN32
  if (!VirtualFree(block, 0, MEM_RELEASE)) goto err;
#endif
 err:
  caml_gc_message(0x1000, "unmapping %" ARCH_SIZET_PRINTF_FORMAT "u bytes"
                  " at %p failed\n", size, block);
}

/* Wrapped functions */

static struct skiplist mmaped_areas = SKIPLIST_STATIC_INITIALIZER;

void caml_mem_unreserve_all(void)
{
  FOREACH_SKIPLIST_ELEMENT(elem, &mmaped_areas, {
      char *block = (char *)elem->key;
      asize_t size = (asize_t)elem->data;
      caml_gc_message(0x1000, "unmapping %" ARCH_SIZET_PRINTF_FORMAT "u bytes"
                              " at %p\n",
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
    caml_gc_message(0x1000, "reserving %" ARCH_SIZET_PRINTF_FORMAT "u bytes"
                            " with alignment %" ARCH_SIZET_PRINTF_FORMAT "u"
                            " failed\n",
                    size, align);
    return NULL;
  }
  CAMLassert_aligned(mem, align);
  caml_gc_message(0x1000, "reserved %" ARCH_SIZET_PRINTF_FORMAT "u bytes with"
                          " alignment %" ARCH_SIZET_PRINTF_FORMAT "u "
                          "at %p for heaps\n", size, align, mem);
  /* remember the mmaped area for cleanup at exit */
  caml_skiplist_insert(&mmaped_areas, (uintnat)mem, (uintnat)size);
  return mem;
}

/* can be used to recommit (preserves already-committed mapping) */
bool caml_mem_commit_os(char *block, asize_t size)
{
  caml_gc_message(0x1000, "committing %" ARCH_SIZET_PRINTF_FORMAT "u bytes"
                          " at %p for heaps\n",
                  size, block);
  return mem_commit_os(block, size);
}

void caml_mem_decommit_os(char * block, asize_t size)
{
  if (size == 0) return;
  caml_gc_message(0x1000, "decommitting %" ARCH_SIZET_PRINTF_FORMAT "u bytes"
                          " at %p for heaps\n",
                  size, block);
  mem_decommit_os(block, size);
}
