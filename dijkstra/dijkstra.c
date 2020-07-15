#include <stdlib.h>
#include <limits.h>
#include <stdio.h>
#include <time.h>
#include "../priq/priq_arr.h"

#define SIZE 8  // number of vertices
#define CONN 3  // the connectedness. 1 is 100%, higher numbers mean less connected
#define INFL 50 // increase this to inflate the highest possible cost, thus creating greater ranges
#define IFTY INT_MAX - INT_MAX/SIZE


 
/* ************************************************** */
/*   Dijkstra's Algorithm to find the shortest path   */
/*  from a single source to all possible destinations */
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
            graph[i][j] = (i==j) ? 0 : (random > INFL) ? IFTY : 1 + random; // so the rest will be INF
        }
    }
}

// Used only for testing, will be removed eventually.
void print_graph (int graph[SIZE][SIZE], int src) {
    int i, j;
    for (i = 0; i < SIZE; i++) {
        for (j = 0; j < SIZE; j++)
            graph[i][j] == IFTY? printf("-\t"): printf("%d\t", graph[i][j]);
        printf ("\n");
    }
    printf("Source: %d\n\n", src);
}


/* ******** */
/* Solution */
/* ******** */

void printPath (int curr, int src, int prev[SIZE]) {
    if (curr == src) {
        printf("%d\t", curr);
    } else {
        printPath (prev[curr], src, prev); printf("%d\t", curr);
    }
} 

void getPaths (int src, int dist[SIZE], int prev[SIZE]) {
    int i;
    for (i = 0; i < SIZE; i++) {
        if (i != src && dist[i] < IFTY) {
            printf("\nTravel from %d to %d at cost %d via: ", src, i, dist[i]);
            printPath(i, src, prev);
        }
    }
}

void dijkstra (int graph[SIZE][SIZE], int src, int *dist, int *prev) {
    int pq[SIZE];
    int i, j, u, cost;
    for (i = 0; i < SIZE; i++) {
        dist[i] = IFTY;  // Best-known distance from src to i
        prev[i] = IFTY;  // Last vertex visited before i
        push(i, IFTY, pq);  // Everybody goes in the queue  
    }
    dist[src] = 0;
    prev[src] = src;
    adjustWeight(src, 0, pq); // special values for src
    while (!pq_emp(pq)) {
        u = popMin(pq);  // src -> u is optimal. relax u's neighbors, then done with u.
        // printf("Popped vertex %d\n", u); 
        if (dist[u] == IFTY) break; // we're running on gas; there are no more reachable vertices 
        for (i = 0; i < SIZE; i++) {
            cost = graph[u][i]; 
            if (cost < IFTY) { // i.e. node i is a neighbor of mine
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
    int i, j;
    srand((unsigned int) time(NULL));
    int src = rand() % SIZE;
    int graph[SIZE][SIZE];
    setup(graph);
    print_graph(graph, src);
    int prev[SIZE];
    int dist[SIZE];
    dijkstra(graph, src, dist, prev);
    getPaths(src, dist, prev);
    return 0;
}
