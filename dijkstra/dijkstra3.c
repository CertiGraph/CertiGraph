#include <stdlib.h>
#include <limits.h>
#include <stdio.h>
#include <time.h>
#include "../priq/priq_arr.h"

#define SIZE 8  // number of vertices
#define CONN 3  // the connectedness. 1 is 100%, higher numbers mean less connected
#define INFL 50 // increase this to inflate the highest possible cost, thus creating greater ranges
#define INF  1879048192 // INT_MAX - INT_MAX/SIZE

extern void * mallocN (int n);
extern void freeN (void *p);
 
/* ************************************************** */
/*   Dijkstra's Algorithm to find the shortest path   */
/*  from a single source to all possible destinations */
/*  This implementation uses a contiguous 2-d matrix  */
/* ************************************************** */

/* *************************** */
/* Setting up a random problem */
/* *************************** */

void setup (int graph[SIZE][SIZE]) {
    srand((unsigned int) time(NULL));
    int i, j;
    for (i = 0; i < SIZE; i++) {
        for (j = 0; j <= SIZE; j++) {
            int random = rand() % (CONN * INFL); // 1 / CONN of these will be greater than INFL
            graph[i][j] = (i==j) ? 0 : (random > INFL) ? INF : random; // so the rest will be INF
        }
    }
}


void print_graph (int graph[SIZE][SIZE], int src) {
    int i, j;
    for (i = 0; i < SIZE; i++) {
        for (j = 0; j < SIZE; j++)
            graph[i][j] == INF ? printf("-\t"): printf("%d\t", graph[i][j]);
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

int getCell (int graph[SIZE][SIZE], int u, int i) {
    return graph[u][i];
}

void dijkstra (int graph[SIZE][SIZE], int src, int *dist, int *prev) {
    int* pq = init(SIZE);
    int i, j, u, cost;
    for (i = 0; i < SIZE; i++) {
        dist[i] = INF;  // Best-known distance from src to i
        prev[i] = INF;  // Last vertex visited before i
        push(i, INF, pq);  // Everybody goes in the queue  
    }
    dist[src] = 0;
    prev[src] = src;
    adjustWeight(src, 0, pq); // special values for src
    while (!pq_emp(SIZE, INF, pq)) {
        u = popMin(SIZE, INF, pq);  // src -> u is optimal. relax u's neighbors, then done with u.
        for (i = 0; i < SIZE; i++) {
            cost = getCell(graph, u, i); 
            if (cost < INF) { // i.e. node i is a neighbor of mine
                if (dist[i] > dist[u] + cost) {  // if we can improve the best-known dist from src to i
                    dist[i] = dist[u] + cost;  // improve it
                    prev[i] = u;  // note that we got there via 'u'
                    adjustWeight(i, dist[i], pq); // and stash the improvement in the PQ
                }
            }
        }
    }
    freePQ(pq);
    return;
}

int main(int argc, const char * argv[])
{
    srand((unsigned int) time(NULL));
    int src = rand() % SIZE;
    int graph[SIZE][SIZE];
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