#include <stdlib.h>
#include <limits.h>
#include <stdio.h>
#include <time.h>

#define SIZE 8  // number of vertices
#define CONN 3  // the connectedness. 1 is 100%, higher numbers mean less connected
#define INFL 50 // increase this to inflate the highest possible cost, thus creating greater ranges
#define IFTY INT_MAX - INT_MAX/SIZE

/* ****************************** */
/*    Array Masquerading as PQ    */
/* ****************************** */

// Here for completeness. Actually just inlined in the code.
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

// // Here for completeness. Actually just inlined in the code.
// void adjustWeight (int vertex, int newWeight, int **pq) {
//     *pq[vertex] = newWeight;
// }

// Quick utility function to check if the PQ empty
// If all cells are IFTY, the pq is considered empty
int pq_emp (int pq[SIZE]) {
    int i;
    for (i = 0; i < SIZE; i++) {
        if (pq[i] < IFTY) // this cell is populated. pq is not empty.
            return 0;
    }   
    return 1;
}
 
/* ************************************************** */
/*   Dijkstra's Algorithm to find the shortest path   */
/*  from a single source to all possible destinations */
/* ************************************************** */

/* *************************** */
/* Setting up a random problem */
/* *************************** */

// not currently used.
// will figure out how to reason about random later.
void setup (int graph[SIZE][SIZE]) {
    srand((unsigned int) time(NULL));
    // src = rand() % SIZE;
    int i, j;
    for (i = 0; i < SIZE; i++) {
        for (j = 0; j <= SIZE; j++) {
            int random = rand() % (CONN * INFL); // 1/CONN of these will be greater than INFL
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
    // int dist[SIZE];
    // int prev[SIZE];
    int pq[SIZE];
    int i, j, u, cost;
    for (i = 0; i < SIZE; i++) {
        dist[i] = IFTY;                   // Best-known distance from src to i
        prev[i] = IFTY;                   // Last vertex visited before i
        pq[i] = IFTY;                     // Everybody goes in the queue
    }
    dist[src] = 0;
    pq[src] = 0;
    prev[src] = src;
    while (!pq_emp(pq)) {
        u = popMin(pq);  // src -> u is optimal. relax u's neighbors if we can, and then forget about u.
        // printf("Popped vertex %d\n", u); 
        for (i = 0; i < SIZE; i++) {
            cost = graph[u][i]; 
            if (cost < IFTY) { // i.e. node i is a neighbor of mine. do I need to add that cost > 0?
                if (dist[i] > dist[u] + cost) { // if we can improve the best-known dist from src to i
                    dist[i] = dist[u] + cost;   // improve it
                    prev[i] = u;                       // note that we got there via 'u'
                    pq[i] = dist[i];                   // and stash the improvement in the PQ
                    // printf("Improved %d --> %d to %d\n", src, i, dist[i]);
                    // uncomment the above line to see how the "best answer" improves slowly!
                }
            } // [src --> i] may NOT be perfect. 
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
    // for (i = 0; i < SIZE; i++) {
    //     for (j = 0; j < SIZE; j++) {
    //         graph[i][j] = 5;
    //     }
    // }
    setup(graph);
    print_graph(graph, src);
    int prev[SIZE];
    int dist[SIZE];
    dijkstra(graph, src, dist, prev);
    getPaths(src, dist, prev);
    return 0;
}