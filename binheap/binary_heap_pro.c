#include <stdlib.h>
#include "binary_heap_pro.h"

#define ROOT_IDX       0u
#define LEFT_CHILD(x)  (2u * x) + 1u
#define RIGHT_CHILD(x) 2u * (x + 1u)
#define PARENT(x)      (x - 1u) / 2u

/* I'm assuming a decent compiler will inline the next two functions; if not they can be made #define macros. */
void exch(unsigned int j, unsigned int k, Item arr[], unsigned int lookup[]) {
  int priority = arr[j].priority;
  int data = arr[j].data;
  unsigned int key1 = arr[j].key;
  unsigned int key2 = arr[k].key;
  arr[j].priority = arr[k].priority;
  arr[j].data = arr[k].data;
  arr[j].key = key2;
  lookup[key2] = j;
  arr[k].priority = priority;
  arr[k].data = data;
  arr[k].key = key1;
  lookup[key1] = k;
}

unsigned int pq_size(PQ *pq) {
  return pq->first_available;
}

unsigned int capacity(PQ *pq) {
  return pq->capacity;
}

int less(unsigned int j, unsigned int k, Item arr[]) {
  return (arr[j].priority <= arr[k].priority);
}

void swim(unsigned int k, Item arr[], unsigned int lookup[]) {
  while (k > ROOT_IDX && less (k, PARENT(k), arr)) {
    exch(k, PARENT(k), arr, lookup);
    k = PARENT(k);
  }
}

void sink (unsigned int k, Item arr[], unsigned int first_available, unsigned int lookup[]) {
  while (LEFT_CHILD(k) < first_available) { /* Requirement that capacity <= MAX_SIZE be of reasonable size */
    unsigned j = LEFT_CHILD(k);
    if (j+1 < first_available && less(j+1, j, arr)) j++; /* careful with j+1 overflow? */
    if (less(k, j, arr)) break;
    exch(k, j, arr, lookup);
    k = j;
  }
}

unsigned int pq_insert_nc(PQ *pq, int priority, int data) {
  unsigned int fa = pq->first_available;
  Item* cells = pq->heap_cells;

  unsigned int key = cells[fa].key;
  cells[fa].priority = priority;
  cells[fa].data = data;
  
  swim(fa, cells, pq->key_table);
  pq->first_available = fa + 1;
  
  return key;
}

void pq_edit_priority(PQ *pq, int key, int newpri) {
  unsigned int* table = pq->key_table;
  Item* cells = pq->heap_cells;
  unsigned int target = table[key];
  // if (target >= pq_size(pq)) return;
  // I will now know that this key refers to a valid member of the heap
  int oldpri = cells[target].priority;

  cells[target].priority = newpri;
  if (newpri <= oldpri) swim(target, cells, table); 
     // potentially unnecessary swimming in case of equality
  else sink (target, cells, pq->first_available, table);
}
// post condition: either the key was in the heap and we did all this stuff,
                   // or we did nothing

void pq_remove_min_nc(PQ *pq, Item* item) {
  /*  unsigned int fa = pq->first_available - 1;
  Item* cells = pq->heap_cells;
  unsigned* lookup = pq->key_table;
  
  exch(ROOT_IDX, fa, cells, lookup);
  item->priority = cells[fa].priority;
  item->data = cells[fa].data;
  item->key = cells[fa].key;

  sink(ROOT_IDX, cells, fa, lookup);
  pq->first_available = fa; */
  pq->first_available--;
  exch(ROOT_IDX, pq->first_available, pq->heap_cells, pq->key_table);
  item->priority = pq->heap_cells[pq->first_available].priority;
  item->data = pq->heap_cells[pq->first_available].data;
  item->key = pq->heap_cells[pq->first_available].key;
  sink(ROOT_IDX, pq->heap_cells, pq->first_available, pq->key_table);
}  

unsigned int pq_insert(PQ *pq, int priority, int data) {
  if (pq->first_available == pq->capacity) return 0; /* Hrm, maybe should signal error or grow heap or whatever... */
  return pq_insert_nc(pq, priority, data);
}

Item* pq_remove_min(PQ *pq) {
  if (pq->first_available == ROOT_IDX) return 0;
  Item* item = (Item*) malloc(sizeof(Item));
  pq_remove_min_nc(pq, item);
  return item;
}

PQ* pq_make(unsigned int size) { /* could take a size parameter I suppose... */
  PQ *pq = (PQ*) mallocN(sizeof(PQ));
  unsigned int* table = (unsigned int*) mallocN(sizeof(unsigned int) * size);
  Item* arr = (Item*) mallocN(sizeof(Item) * size);
  int i; 
  for (i = 0; i < size; i++) {
    arr[i].key = i;
    arr[i].priority = 0;
    arr[i].data = 0;
    table[i] = i;
  }

  pq->capacity = size;
  pq->first_available = 0;
  pq->heap_cells = arr;
  pq->key_table = table;

  return pq;
}

void pq_free (PQ *pq) {
    freeN(pq->key_table);
    freeN(pq->heap_cells);
    freeN(pq);
}

/* could imagine adding some additonal functions:
     heapify
     ?
*/
