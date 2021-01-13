#ifndef __BINARY_HEAP_PRO_H__
#define __BINARY_HEAP_PRO_H__

// #define INITIAL_SIZE 8 /* Probably should be a power of 2, no more than max_int / 2 - 1? */
#define MAX_SIZE (1 << 29) /* for 32-bit machine, is this the best we can do? */

typedef struct structItem {
  unsigned int key; /* make const? */
  int priority;
  void* data; /* Should this be a union of void* and int? */
} Item;

typedef struct structPQ {
  unsigned int capacity;
  unsigned int first_available;
  Item* heap_cells;
  unsigned int* key_table;
} PQ;

void remove_min_nc(PQ *pq, Item *item);
unsigned int insert_nc(PQ *pq, int priority, void* data);

unsigned int insert(PQ *pq, int priority, void* data);
Item* remove_min(PQ *pq);
void edit_pri(PQ *pq, int key, int newpri);

unsigned int capacity(PQ *pq);
unsigned int pq_size(PQ *pq);

PQ* make();
/*
 void insert(PQ *pq, Item *x);
 Item* remove_min(PQ *pq);
*/
/* void free_pq(PQ *pq); */

#endif
