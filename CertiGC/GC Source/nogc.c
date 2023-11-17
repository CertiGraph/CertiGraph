#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include <assert.h>
#include "config.h"
#include "values.h"
#include "gc_stack.h"

/* WARNING: THIS PROGRAM HAS NOT BEEN TESTED since its overhaul 17 November 2023 */

/* This is an alternate implementation of the gc.h interface,
   that does no garbage collection.  Useful for debugging 
   both programs and proofs. */

#define SIZE (1<<24)  /* 16 million words */

struct heapx {
  value space [SIZE];
};

void garbage_collect(struct thread_info *ti) {
  struct heapx *h = (struct heapx *)ti->heap;
  if (h==NULL) {
    /* If the heap has not yet been initialized, create it */
    h = (struct heapx *) malloc (sizeof *h);
    ti->alloc = h->space;
    ti->limit = h->space+SIZE;
    ti->heap = (struct heap *) h;
    if (ti->nalloc > ti->limit - ti->alloc) {
       fprintf(stderr, "Heap is too small for function's num_allocs\n");
       exit(1);
    }
  } else {
    fprintf(stderr, "Ran out of heap, and no garbage collector present!\n");
    exit(1);
  }
}
  

void free_heap(struct heap *h) {
  struct heapx *h1 = (struct heapx *) h;
  free(h1);
}

void reset_heap(struct heap *h) {
  fprintf(stderr, "reset_heap not supported\n");
  exit(1);
}
