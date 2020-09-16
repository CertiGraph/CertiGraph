#include "priq_arr.h"


/* ****************************** */
/*    Array Masquerading as PQ    */
/* ****************************** */


void push (int vertex, int weight, int pq[SIZE]) {
    pq[vertex] = weight;   
}

// precondition: won't be called on an empty PQ
int popMin (int pq[SIZE]) {
    int minVertex = 0;
    int minWeight = pq[minVertex];
    int i;
    for (i = 0; i < SIZE; i++) {
        if (pq[i] < minWeight) {
            minVertex = i;
            minWeight = pq[i];
        }   
    }
    pq[minVertex] = IFTY+1;
    return minVertex;
}

void adjustWeight (int vertex, int newWeight, int pq[SIZE]) {
    pq[vertex] = newWeight;
}

// Quick utility function to check if the PQ is empty
int pq_emp (int pq[SIZE]) {
    int i;
    for (i = 0; i < SIZE; i++) {
        if (pq[i] < IFTY+1) // this cell is populated. pq is not empty.
            return 0;
    }   
    return 1;
}
