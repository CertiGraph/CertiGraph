//
//  dijkstra.c
//  Dijkstra
//
//  Created by Anshuman Mohan on 14/6/19.
//  Copyright © 2019 Anshuman Mohan. All rights reserved.
//

#include "dijkstra.h"
#include "linked_list.h"
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

#define INF INT_MAX
#define SIZE 8 // number of vertices
#define CONN 4 // the connectedness. 1 is 100%, higher numbers mean less connected

/*
 * Dijkstra's Algorithm to find the shortest path
 * from a single source to all possible destinations
 */

/* *************************** */
/* Setting up a random problem */
/* *************************** */

int graph[SIZE][SIZE]; /* We represent the graph using an adjacency matrix */
int src, dst;

void setup () {
    srand((uint) time(NULL));
    src = rand() % SIZE;
    int i, j;
    for (i = 0; i < SIZE; i++) {
        for (j = 0; j <= SIZE; j++) {
            int random = rand() % (CONN * SIZE); // roughly 1/CONN of these will be greater than SIZE
            graph[i][j] = (i==j) ? 0 : (random > SIZE) ? INF : 1 + random; // so the rest will be INF
        }
    }
}

// Used only for testing, will be removed eventually.
void print_graph () {
    int i, j;
    for (i = 0; i < SIZE; i++) {
        for (j = 0; j < SIZE; j++)
            graph[i][j] == INF? printf("-\t"): printf("%d\t", graph[i][j]);
        printf ("\n");
    }
    printf("Source: %d\n\n", src);
}


/* ******** */
/* Solution */
/* ******** */

int dist[SIZE];
int prev[SIZE];

void dijkstra () {
    int i, u;
    struct Node *pq = NULL;
    for (i = 0; i < SIZE; i++) {
        dist[i] = (i == src) ? 0 : INF;  // Best-known distance from src to i
        prev[i] = INF;                   // Last vertex visited before i
        push(i, dist[i], &pq);           // Everybody goes in the queue
    }
    while (pq != NULL) {
        u = popMin(&pq); // this is the next candidate we will deal with (once and for all)
        if (u < 0) { // The "min" actually had distance infinity. All the rest in the PQ are unreachable.
            printf("\nThe following vertices were altogether unreachable:\n");
            print_verts(pq);
            break;
        }
        for (i = 0; i < SIZE; i++) {
            if ((graph[u][i]) < INF) { // i.e. node i is a neighbor of mine
                if (dist[i] > dist[u] + graph[u][i]) { // if we can improve the best-known dist from src to i
                    dist[i] = dist[u] + graph[u][i];   // improve it
                    prev[i] = u;                       // note that we got there via 'u'
                    adjustWeight(i, dist[i], &pq);     // and then stash the improvement in the PQ
                    printf("Improved the dist to get to vertex %d to %d\n", i, dist[i]); // for testing only
                }
            }
        }
    }
}
