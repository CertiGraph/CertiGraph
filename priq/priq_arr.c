#include <stdlib.h>
#include "priq_arr.h"

/* ****************************** */
/*    Array Masquerading as PQ    */
/* ****************************** */

int* init (int size) {
    int* pq = mallocN (size * sizeof *pq);
    return pq;
}

// precondition: vertex < size
void push (int vertex, int weight, int* pq) {
    pq[vertex] = weight;   
}

// precondition: won't be called on an empty PQ
int popMin (int size, int inf, int* pq) {
    int minVertex = 0;
    int minWeight = pq[minVertex];
    int i;
    for (i = 0; i < size; i++) {
        if (pq[i] < minWeight) {
            minVertex = i;
            minWeight = pq[i];
        }   
    }
    pq[minVertex] = inf+1;
    return minVertex;
}

void adjustWeight (int vertex, int newWeight, int* pq) {
    pq[vertex] = newWeight;
}

// Quick utility function to check if the PQ is empty
int pq_emp (int size, int inf, int* pq) {
    int i;
    for (i = 0; i < size; i++) {
        if (pq[i] < inf+1) // this cell is populated. pq is not empty.
            return 0;
    }   
    return 1;
}

void freePQ (void* pq) {
    free(pq);
}

/*
int main () {
    return 0;
}
*/