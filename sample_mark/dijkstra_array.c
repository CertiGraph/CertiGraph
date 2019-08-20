#include <stdlib.h>
#include <limits.h>
#include <stdio.h>
#include <time.h>

#define IFTY INT_MAX
#define SIZE 8  // number of vertices
#define CONN 1  // the connectedness. 1 is 100%, higher numbers mean less connected
#define INFL 50 // increase this to inflate the highest possible cost, thus creating greater ranges


/* ****************************** */
/*    Array Masquerading as PQ    */
/* ****************************** */


int pq[SIZE];

// Here for completeness. Actually just inlined in the code.
void push (int vertex, int weight) {
    pq[vertex] = weight;   
}

int popMin () {
    int minWeight = IFTY;
    int minVertex = -1;
    int i;
    for (i = 0; i < SIZE; i++) {
        if (pq[i] < minWeight) {
            minVertex = i;
            minWeight = pq[i];
        }   
    }
    if (minVertex != -1) {
        pq[minVertex] = IFTY; /* basically, deletes the node */
    }
    return minVertex;
}

// Here for completeness. Actually just inlined in the code.
void adjustWeight (int vertex, int newWeight) {
    pq[vertex] = newWeight;
}

// Quick utility function to check that the PQ is not empty
int pq_not_emp () {
    int i;
    for (i = 0; i < SIZE; i++) {
        if (pq[i] < IFTY)
            return 1;
    }   
    return 0;
}
 
/* ************************************************** */
/*   Dijkstra's Algorithm to find the shortest path   */
/*  from a single source to all possible destinations */
/* ************************************************** */

/* *************************** */
/* Setting up a random problem */
/* *************************** */

int graph[SIZE][SIZE]; /* We represent the graph using an adjacency matrix */
int src, dst;

void setup () {
    srand((unsigned int) time(NULL));
    src = rand() % SIZE;
    int i, j;
    for (i = 0; i < SIZE; i++) {
        for (j = 0; j <= SIZE; j++) {
            int random = rand() % (CONN * INFL); // 1/CONN of these will be greater than INFL
            graph[i][j] = (i==j) ? 0 : (random > INFL) ? IFTY : 1 + random; // so the rest will be INF
        }
    }
}


/*
// Used only for testing, will be removed eventually.
void print_graph () {
    int i, j;
    for (i = 0; i < SIZE; i++) {
        for (j = 0; j < SIZE; j++)
            graph[i][j] == IFTY? printf("-\t"): printf("%d\t", graph[i][j]);
        printf ("\n");
    }
    printf("Source: %d\n\n", src);
}
*/


/* ******** */
/* Solution */
/* ******** */

int dist[SIZE];
int prev[SIZE];

void dijkstra () {
    int i, u;
    // struct Node *pq = NULL;
    for (i = 0; i < SIZE; i++) {
        dist[i] = (i == src) ? 0 : IFTY;  // Best-known distance from src to i
        prev[i] = IFTY;                   // Last vertex visited before i
        pq[i] = dist[i];                  // Everybody goes in the queue
    }
    while (pq_not_emp()) {
        u = popMin();  // this is the next candidate we will deal with (once and for all)
        if (u == -1)    // The "min" actually had distance infinity. All the rest in the PQ are unreachable.
            break;
        for (i = 0; i < SIZE; i++) {
            if ((graph[u][i]) < IFTY) { // i.e. node i is a neighbor of mine
                if (dist[i] > dist[u] + graph[u][i]) { // if we can improve the best-known dist from src to i
                    dist[i] = dist[u] + graph[u][i];   // improve it
                    prev[i] = u;                       // note that we got there via 'u'
                    pq[i] = dist[i];                   // and then stash the improvement in the PQ
                    // printf("Improved %d --> %d to %d\n", src, i, dist[i]);
                    // uncomment the above line to see how the "best answer" improves slowly!
                }
            }
        }
    }
}

/*
void printPath (int curr) {
    if (curr == src) {
        printf("%d\t", curr);
    } else {
        printPath (prev[curr]); printf("%d\t", curr);
    }
} 

void getPaths () {
    int i;
    for (i = 0; i < SIZE; i++) {
        if (i != src && dist[i] < IFTY) {
            printf("\nTravel from %d to %d at cost %d via: ", src, i, dist[i]);
            printPath(i);
        }
    }
}
*/

int main(int argc, const char * argv[])
{
    setup();
    // print_graph();
    dijkstra();
    // getPaths();
    return 0;
}