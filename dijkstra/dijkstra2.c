#include <stdlib.h>
#include <limits.h>
#include <stdio.h>
#include <time.h>
#include "../binheap/binary_heap_pro.h"

#define SIZE 8  // number of vertices
#define CONN 3  // the connectedness. 1 is 100%, higher numbers mean less connected
#define INFL 50 // increase this to inflate the highest possible cost, thus creating greater ranges
#define INF  2147483647 // INT_MAX
#define graph(i, j) (graph[(i) * SIZE + (j)])
 
/* ************************************************** */
/*   Dijkstra's Algorithm to find the shortest path   */
/*  from a single source to all possible destinations */
/*  This implementation uses a contiguous 1-d matrix  */
/* ************************************************** */

/* *************************** */
/* Setting up a random problem */
/* *************************** */

void setup (int graph[SIZE*SIZE]) {
    srand((unsigned int) time(NULL));
    int i, j;
    for (i = 0; i < SIZE; i++) {
        for (j = 0; j <= SIZE; j++) {
            int random = rand() % (CONN * INFL); // 1 / CONN of these will be greater than INFL
            graph(i,j) = (i==j) ? 0 : (random > INFL) ? INF : random; // so the rest will be INF
        }
    }
}


void print_graph (int graph[SIZE * SIZE], int src) {
    int i, j;
    for (i = 0; i < SIZE; i++) {
        for (j = 0; j < SIZE; j++)
            graph(i,j) == INF ? printf("-\t"): printf("%d\t", graph(i,j));
        printf ("\n");
    }
    printf("Size: %d\nSource: %d\n\n", SIZE, src);
}


/* ******** */
/* Solution */
/* ******** */

void printPath (int curr, int src, int* prev) {
    if (curr == src) {
        printf("%d\t", curr);
    } else {
        printPath (prev[curr], src, prev); printf("%d\t", curr);
    }
} 

void getPaths (int src, int* dist, int* prev) {
    int i;
    for (i = 0; i < SIZE; i++) {
        if (i != src && dist[i] < INF) {
            printf("\nTravel from %d to %d at cost %d via: ", src, i, dist[i]);
            printPath(i, src, prev);
        }
    }
    printf("\nThe rest are unreachable.\n");
}

int getCell (int graph[SIZE*SIZE], int u, int i) {
    return graph(u,i);
}

void dijkstra (int graph[SIZE*SIZE], int src, int *dist, int *prev) {
    Item* temp = (Item*) mallocN(sizeof(Item));
    int* keys = mallocN (SIZE * sizeof (int));
    PQ* pq = pq_make(SIZE); 
    int i, j, u, cost;
    for (i = 0; i < SIZE; i++) {
        dist[i] = INF;  // Best-known distance from src to i
        prev[i] = INF;  // Last vertex visited before i
        keys[i] = pq_insert_nc(pq, INF, i); // Insert everyone, plus store keys locally
    }
    dist[src] = 0;
    prev[src] = src;
    pq_edit_priority(pq, keys[src], 0); // special value for src
    while (pq_size(pq) > 0) {
        pq_remove_min_nc(pq, temp);
        u = temp->data; // src -> u is optimal. relax u's neighbors, then done with u.
        for (i = 0; i < SIZE; i++) {
            cost = getCell(graph, u, i); 
            if (cost < INF) { // i.e. node i is a neighbor of mine
                if (dist[i] > dist[u] + cost) {  // if we can improve the best-known dist from src to i
                    dist[i] = dist[u] + cost;  // improve it
                    prev[i] = u;  // note that we got there via 'u'
                    pq_edit_priority(pq, keys[i], dist[i]); // and stash the improvement in the PQ
                }
            }
        }
    }
    freeN (temp);
    pq_free (pq);
    freeN (keys);
    return;
}

int main(int argc, const char * argv[])
{
    srand((unsigned int) time(NULL));
    int src = rand() % SIZE;
    int graph[SIZE*SIZE];
    setup(graph);
    print_graph(graph, src);
    int* prev = mallocN (SIZE * sizeof *prev);
    int* dist = mallocN (SIZE * sizeof *dist);
    dijkstra(graph, src, dist, prev);
    getPaths(src, dist, prev);
    free(prev);
    free(dist);
    return 0;
}