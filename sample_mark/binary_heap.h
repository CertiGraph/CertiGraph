#ifndef __BINARY_HEAP_H__
#define __BINARY_HEAP_H__

#define INITIAL_SIZE 8 /* Probably should be a power of 2, no more than max_int / 2 - 1? */
#define MAX_SIZE (1 << 29) /* for 32-bit machine, is this the best we can do? */

#define ROOT_IDX       0
#define LEFT_CHILD(x)  (2 * x) + 1
#define RIGHT_CHILD(x) LEFT_CHILD(x) + 1
#define PARENT(x)      (x - 1) / 2

typedef struct structItem {
  int priority;
  void* data; /* Should this be a union of void* and int? */
} Item;

typedef struct structPQ {
  unsigned int capacity;
  unsigned int first_available;
  Item* heap_cells;
} PQ;

PQ* make();
void insert(PQ *pq, Item *x);
Item* remove_min(PQ *pq);
unsigned int capacity(PQ *pq);
void free_pq(PQ *pq);

#endif