#ifndef __BINARY_HEAP_PRO_H__
#define __BINARY_HEAP_PRO_H__

extern void * mallocN (int n); /* Maybe there are better choices for allocators? */
extern void freeN (void* p); /* Maybe there are better choices for deallocators? */

// #define INITIAL_SIZE 8 /* Probably should be a power of 2, no more than max_int / 2 - 1? */
#define MAX_SIZE (1 << 29) /* for 32-bit machine, is this the best we can do? */

typedef struct structItem {
  unsigned int key; /* make const? */
  int priority;
  int data; /* Should this be a union of void* and int? */
} Item;

typedef struct structPQ {
  unsigned int capacity;
  unsigned int first_available;
  Item* heap_cells;
  unsigned int* key_table;
} PQ;

void pq_remove_min_nc(PQ *pq, Item *item);
unsigned int pq_insert_nc(PQ *pq, int priority, int data);

unsigned int pq_insert(PQ *pq, int priority, int data);
Item* pq_remove_min(PQ *pq);
void pq_edit_priority(PQ *pq, int key, int newpri);

unsigned int capacity(PQ *pq);
unsigned int pq_size(PQ *pq);

PQ* pq_make(unsigned int size);
void pq_free (PQ *pq);
/*
 void insert(PQ *pq, Item *x);
 Item* remove_min(PQ *pq);
*/
/* void free_pq(PQ *pq); */

#endif
