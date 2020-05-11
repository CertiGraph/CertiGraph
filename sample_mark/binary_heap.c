#define MAX_SIZE 8 /* Probably should be a power of 2, no more than max_int / 2 - 1? */
#define SIZE_IDX 0
#define ROOT_IDX 1

/* #define less */

typedef struct pqItem {
  int priority;
  void* data;
} Item;

void exch(unsigned int j, unsigned int k, Item* arr[]) {
  Item* t = arr[j];
  arr[j] = arr[k];
  arr[k] = t;
}

/* If this doesn't work with clightgen, we can use the #define method. */
int less(unsigned int j, unsigned int k, Item* arr[]) {
  return (arr[j]->priority <= arr[k]->priority);
}

void swim(unsigned int k, Item* arr[]) {
  while (k > 1 && less (k/2, k, arr)) {
    exch(k, k/2, arr);
    k = k/2;
  }
}

void sink (unsigned int k, Item* arr[]) {
  int size = (unsigned int) arr[SIZE_IDX]; /* Hrm... */
  while (2 * k <= size) { /* Requirement that size <= MAX_SIZE be of reasonable size */ /* < size or <= size? */
    unsigned j = 2 * k;
    if (j < size && less(j, j+1, arr)) j++; /* careful with j+1 overflow? */
    if (less(j, k, arr)) break;
    exch(k, j, arr);
    k = j;
  }
}

void insert(Item* arr[], Item* x) {
  int size = (unsigned int) arr[SIZE_IDX]; /* Hrm... */
  if (size >= MAX_SIZE) return; /* Hrm */
  arr[size] = x;
  arr[SIZE_IDX] = arr[SIZE_IDX] + 1;
  swim(size, arr);
}

Item* remove_min(Item* arr[]) {
  int size = (unsigned int) arr[SIZE_IDX]; /* Hrm... */
  if (size == ROOT_IDX) return 0;
  Item* item = arr[size - 1];
  exch(ROOT_IDX,size - 1,arr);
  arr[SIZE_IDX] = arr[SIZE_IDX] - 1;
  sink(ROOT_IDX, arr);
  return item;
}

/* could imagine adding some additonal functions:
     heapify
     size
     ?
*/
