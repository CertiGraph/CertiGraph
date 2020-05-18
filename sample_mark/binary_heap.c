#include "binary_heap.h"
extern void * mallocN (int n); /* Maybe there are better choices for allocators? */
/*
#define INITIAL_SIZE 8
#define MAX_SIZE (1 << 29)

#define ROOT_IDX       0
#define LEFT_CHILD(x)  (2 * x) + 1
#define RIGHT_CHILD(x) LEFT_CHILD(x) + 1
#define PARENT(x)      (x - 1) / 2

typedef struct structItem {
  int priority;
  void* data;
} Item;

typedef struct structPQ {
  unsigned int capacity;
  unsigned int first_available;
  Item* heap_cells;
} PQ;
*/

#define ROOT_IDX       0u
#define LEFT_CHILD(x)  (2u * x) + 1u
#define RIGHT_CHILD(x) LEFT_CHILD(x) + 1u
#define PARENT(x)      (x - 1u) / 2u

/* I'm assuming a decent compiler will inline the next two functions; if not they can be made #define macros. */
void exch(unsigned int j, unsigned int k, Item arr[]) {
  int priority = arr[j].priority;
  void* data = arr[j].data;
  arr[j].priority = arr[k].priority;
  arr[j].data = arr[k].data;
  arr[k].priority = priority;
  arr[k].data = data;
}

int less(unsigned int j, unsigned int k, Item arr[]) {
  return (arr[j].priority <= arr[k].priority);
}

void swim(unsigned int k, Item arr[]) {
  while (k > ROOT_IDX && less (k, PARENT(k), arr)) {
    exch(k, PARENT(k), arr);
    k = PARENT(k);
  }
}

void sink (unsigned int k, Item arr[], unsigned int first_available) {
  while (LEFT_CHILD(k) < first_available) { /* Requirement that capacity <= MAX_SIZE be of reasonable size */
    unsigned j = LEFT_CHILD(k);
    if (j+1 < first_available && less(j+1, j, arr)) j++; /* careful with j+1 overflow? */
    if (less(k, j, arr)) break;
    exch(k, j, arr);
    k = j;
  }
}

void insert_nc(PQ *pq, Item *x) {
  pq->heap_cells[pq->first_available].priority = x->priority;
  pq->heap_cells[pq->first_available].data = x->data;
  swim(pq->first_available, pq->heap_cells);
  pq->first_available++;
}

void insert(PQ *pq, Item *x) {
  if (pq->first_available == pq->capacity) return; /* Hrm, maybe should signal error or grow heap or whatever... */
  insert_nc(pq, x);
}

void remove_min_nc(PQ *pq, Item* item) {
  pq->first_available--;
  exch(ROOT_IDX, pq->first_available, pq->heap_cells);
  item->priority = pq->heap_cells[pq->first_available].priority;
  item->data = pq->heap_cells[pq->first_available].data;
  sink(ROOT_IDX, pq->heap_cells, pq->first_available);
}  

Item* remove_min(PQ *pq) {
  if (pq->first_available == ROOT_IDX) return 0;
  Item* item = (Item*) mallocN(sizeof(Item));
  remove_min_nc(pq, item);
  return item;
}

unsigned int size(PQ *pq) {
  return pq->first_available;
}

unsigned int capacity(PQ *pq) {
  return pq->capacity;
}

PQ* make() { /* could take a size parameter I suppose... */
  Item* arr = (Item*) mallocN(sizeof(Item) * INITIAL_SIZE);
  PQ *pq = (PQ*) mallocN(sizeof(PQ));
  pq->capacity = INITIAL_SIZE;
  pq->first_available = 0;
  pq->heap_cells = arr;
  return pq;
}

/* could imagine adding some additonal functions:
     heapify
     ?
*/
