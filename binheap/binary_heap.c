#include "binary_heap.h"
extern void * mallocN (int n); /* Maybe there are better choices for allocators? */
extern void freeN (void* p); /* Maybe there are better choices for deallocators? */

#define ROOT_IDX       0u
#define LEFT_CHILD(x)  (2u * x) + 1u
#define RIGHT_CHILD(x) 2u * (x + 1u)
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

unsigned int size(PQ *pq) {
  return pq->first_available;
}

unsigned int capacity(PQ *pq) {
  return pq->capacity;
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

void remove_min_nc(PQ *pq, Item* item) {
  pq->first_available--;
  exch(ROOT_IDX, pq->first_available, pq->heap_cells);
  item->priority = pq->heap_cells[pq->first_available].priority;
  item->data = pq->heap_cells[pq->first_available].data;
  sink(ROOT_IDX, pq->heap_cells, pq->first_available);
}  

void build_heap(Item arr[], unsigned int size) {
  unsigned int start = PARENT(size);
  while(1) {
    sink(start, arr, size);
    if (start == 0) break;
    start--;
  }
}

// Note, this will result in a reverse sorted list since we have a min-heap rather than a max-heap.
void heapsort_rev(Item* arr, unsigned int size) {
  // build the heap
  build_heap(arr,size);

  unsigned int active = size;
  while (active > 1) {
    active--;
    exch(ROOT_IDX, active, arr);
    sink(ROOT_IDX, arr, active);
  }
} 

/* Everything above here has been verified. */

void insert(PQ *pq, Item *x) {
  if (pq->first_available == pq->capacity) return; /* Hrm, maybe should signal error or grow heap or whatever... */
  insert_nc(pq, x);
}

Item* remove_min(PQ *pq) {
  if (pq->first_available == ROOT_IDX) return 0;
  Item* item = (Item*) mallocN(sizeof(Item));
  remove_min_nc(pq, item);
  return item;
}

PQ* make(unsigned int size) { /* could take a size parameter I suppose... */
  Item* arr = (Item*) mallocN(sizeof(Item) * size);
  PQ *pq = (PQ*) mallocN(sizeof(PQ));
  pq->capacity = size;
  pq->first_available = 0;
  pq->heap_cells = arr;
  return pq;
}

PQ* heapify(Item* arr, unsigned int size) {
  // First, build the heap within the array
  build_heap(arr,size);

  // Now, malloc the structure
  PQ *pq = (PQ*) mallocN(sizeof(PQ));
  pq->capacity = size;
  pq->first_available = size;
  pq->heap_cells = arr;
  return pq;
}

void pq_free(PQ *pq) {
  freeN(pq->heap_cells);
  freeN(pq);
}

