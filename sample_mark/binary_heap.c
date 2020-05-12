extern void * mallocN (int n); /* Maybe there are better choices for allocators? */

#define INITIAL_SIZE 8 /* Probably should be a power of 2, no more than max_int / 2 - 1? */
#define MAX_SIZE (1 << 29) /* for 32-bit machine, is this the best we can do? */

#define ROOT_IDX       0
#define LEFT_CHILD(x)  (2 * x) + 1
#define RIGHT_CHILD(x) LEFT_CHILD(x) + 1
#define PARENT(x)      (x - 1) / 2

/* #define less */

typedef struct structItem {
  int priority;
  void* data; /* Should this be a union of void* and int? */
} Item;

typedef struct structPQ {
  unsigned int capacity;
  unsigned int first_available;
  Item* heap_cells;
} PQ;

/* I'm assuming a decent compiler will inline the next two functions; if not they can be made #define macros. */
void exch(unsigned int j, unsigned int k, Item arr[]) {
  Item t = arr[j];
  arr[j] = arr[k];
  arr[k] = t;
}

/* If this doesn't work with clightgen, we can use the #define method. */
int less(unsigned int j, unsigned int k, Item arr[]) {
  return (arr[j].priority <= arr[k].priority);
}

void swim(unsigned int k, Item arr[]) {
  while (k > ROOT_IDX && less (PARENT(k), k, arr)) {
    exch(k, PARENT(k), arr);
    k = PARENT(k);
  }
}

void sink (unsigned int k, Item arr[], unsigned int last_used) {
  while (LEFT_CHILD(k) <= last_used) { /* Requirement that capacity <= MAX_SIZE be of reasonable size */
    unsigned j = LEFT_CHILD(k);
    if (j < last_used && less(j + 1, j, arr)) j++; /* careful with j+1 overflow? */
    if (less(j, k, arr)) break;
    exch(k, j, arr);
    k = j;
  }
}

void insert(PQ pq, Item x) {
  if (pq.first_available == pq.capacity) return; /* Hrm, maybe should signal error or grow heap or whatever... */
  pq.heap_cells[pq.first_available] = x;
  swim(pq.first_available, pq.heap_cells);
  pq.first_available++;
}

Item remove_min(PQ pq) {
  /* if (pq.first_available == ROOT_IDX) return 0; */ /* Not sure what to return here... maybe make return type Item*?  */
  pq.first_available--;
  if (pq.first_available == ROOT_IDX) return pq.heap_cells[ROOT_IDX];
  exch(ROOT_IDX, pq.first_available, pq.heap_cells);
  Item item = pq.heap_cells[pq.first_available];
  sink(ROOT_IDX, pq.heap_cells, pq.first_available - 1);
  return item;
}

unsigned int size(PQ pq) {
  return pq.first_available;
}

unsigned int capacity(PQ pq) {
  return pq.capacity;
}

PQ make() { /* could take a size parameter I suppose... */
  Item* arr = (Item*) mallocN(sizeof(Item) * INITIAL_SIZE);
  return (PQ) {.capacity = INITIAL_SIZE, .first_available = 0, .heap_cells = arr};
}

/* could imagine adding some additonal functions:
     heapify
     ?
*/
