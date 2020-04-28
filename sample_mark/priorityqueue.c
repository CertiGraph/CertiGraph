
#include <stdlib.h>
#include <limits.h>

#define SIZE 8
#define IFTY INT_MAX - INT_MAX/SIZE


/* ****************************** */
/*    Array Masquerading as PQ    */
/* ****************************** */

//Actually just inlined in the code, but here is push:
// void push (int vertex, int weight, int** pq) {
//     *pq[vertex] = weight;   
// }


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
    pq[minVertex] = IFTY+1; /* basically, delete the node */
    return minVertex;
}

// Actually just inlined in the code, but here is adjustWeight:
// void adjustWeight (int vertex, int newWeight, int **pq) {
//     *pq[vertex] = newWeight;
// }


// Quick utility function to check if the PQ empty
// If all cells are >= IFTY, the pq is considered empty
int pq_emp (int pq[SIZE]) {
    int i;
    for (i = 0; i < SIZE; i++) {
        if (pq[i] < IFTY) // this cell is populated. pq is not empty.
            return 0;
    }   
    return 1;
}