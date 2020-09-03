#include <stdlib.h>
#include <limits.h>
#include <stdio.h>  
#include <time.h>
#include "../priq/priq_arr.h"

#define CONN 3  // the connectedness. 1 is 100%, higher numbers mean less connected
#define INFL 50 // increase this to inflate the highest possible cost, thus creating greater ranges
 
/* ************************************************** */
/*   Dijkstra's Algorithm to find the shortest path   */
/*  from a single source to all possible destinations */
/* ************************************************** */

/* *************************** */
/* Setting up a random problem */
/* *************************** */


void setup (int** graph, int size, int inf) {
    srand((unsigned int) time(NULL));
    int i, j;
    for (i = 0; i < size; i++) {
        for (j = 0; j <= size; j++) {
            int random = rand() % (CONN * INFL); // 1 / CONN of these will be greater than INFL
            graph[i][j] = (i==j) ? 0 : (random > INFL) ? inf : 1 + random; // so the rest will be INF
        }
    }
}

// Used only for testing, will be removed eventually.
void print_graph (int** graph, int size, int inf, int src) {
    int i, j;
    for (i = 0; i < size; i++) {
        for (j = 0; j < size; j++)
            graph[i][j] == inf ? printf("-\t"): printf("%d\t", graph[i][j]);
        printf ("\n");
    }
    printf("Size: %d\nSource: %d\n\n", size, src);
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

void getPaths (int src, int* dist, int* prev, int size, int inf) {
    int i;
    for (i = 0; i < size; i++) {
        if (i != src && dist[i] < inf) {
            printf("\nTravel from %d to %d at cost %d via: ", src, i, dist[i]);
            printPath(i, src, prev);
        }   
    }
    printf("\nThe rest are unreachable.\n");
}

void dijkstra (int** graph, int src, int *dist, int *prev, int size, int inf) {
    int* pq = malloc (size * sizeof *pq);
    int i, j, u, cost;
    for (i = 0; i < size; i++) {
        dist[i] = inf;  // Best-known distance from src to i
        prev[i] = inf;  // Last vertex visited before i
        push(i, inf, pq);  // Everybody goes in the queue  
    }
    dist[src] = 0;
    prev[src] = src;
    adjustWeight(src, 0, pq); // special values for src
    while (!pq_emp(size, inf, pq)) {
        u = popMin(size, inf, pq);  // src -> u is optimal. relax u's neighbors, then done with u.
        // printf("Popped vertex %d\n", u); 
        // if (dist[u] == IFTY) break; // we're running on gas; there are no more reachable vertices 
        for (i = 0; i < size; i++) {
            cost = graph[u][i]; 
            if (cost < inf) { // i.e. node i is a neighbor of mine
                if (dist[i] > dist[u] + cost) {  // if we can improve the best-known dist from src to i
                    dist[i] = dist[u] + cost;  // improve it
                    prev[i] = u;  // note that we got there via 'u'
                    adjustWeight(i, dist[i], pq); // and stash the improvement in the PQ
                    // printf("Improved %d --> %d to %d\n", src, i, dist[i]);
                    // uncomment the above line to see how the "best answer" improves slowly
                }
            }
        }
    }
    return;
    // return prev;
    // for(i = 0; i < SIZE; i++)
    //     printf("%d\t", prev[i]);
    // printf("\n");
    // getPaths(src, dist, prev);
}

int main(int argc, const char * argv[])
{
    int i;
    srand((unsigned int) time(NULL));
    const int size = 1 + rand() % 20; // cannot allow size = 0. upper limit?
    const int inf = INT_MAX - INT_MAX/size;
    int src = rand() % size; 

    int** graph;
    graph = malloc(size * sizeof *graph);
    for (i=0; i < size; i++) {
        graph[i] = malloc(size * sizeof *graph[i]);
    }

    setup(graph, size, inf);
    print_graph(graph, size, inf, src);
    int* prev = malloc (size * sizeof *prev);
    int* dist = malloc (size * sizeof *dist);
    dijkstra(graph, src, dist, prev, size, inf);
    getPaths(src, dist, prev, size, inf);
    
    free(prev);
    free(dist);
    for (i=0; i < size; i++) {
        free(graph[i]);
    }
    free(graph);

    return 0;
}

// https://stackoverflow.com/questions/3911400/how-to-pass-2d-array-matrix-in-a-function-in-c
