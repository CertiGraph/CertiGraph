#include <stdlib.h>
#include <limits.h>
#include <stdio.h>
#include <time.h>
#include "../priq/priq_arr.h"

#define SIZE 8  // number of vertices
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


// from https://www.geeksforgeeks.org/graph-and-its-representations/
 
struct AdjListNode 
{ 
    int dst; 
    int weight;
    struct AdjListNode* next; 
};

struct AdjList 
{ 
    struct AdjListNode *head;  
};

struct Graph 
{ 
    int size; 
    struct AdjList* array; 
};

struct AdjListNode* newAdjListNode (int dst, int weight) 
{ 
    struct AdjListNode* newNode = (struct AdjListNode*) mallocN(sizeof(struct AdjListNode)); 
    newNode->dst = dst; 
    newNode->weight = weight; 
    newNode->next = NULL; 
    return newNode; 
} 

struct Graph* createGraph(int size) 
{ 
    int i; 
    struct Graph* graph = (struct Graph*) mallocN(sizeof(struct Graph)); 
    graph->size = size; 
    graph->array = (struct AdjList*) mallocN(size * sizeof(struct AdjList)); 
    for (i = 0; i < size; ++i) {
        graph->array[i].head = NULL;   
    }
    return graph; 
}  

void addEdge(struct Graph* graph, int src, int dst, int weight) 
{ 
    struct AdjListNode* newNode = newAdjListNode(dst, weight); 
    newNode->next = graph->array[src].head; 
    graph->array[src].head = newNode; 
} 

void printGraph(struct Graph* graph) 
{ 
    int v; 
    for (v = 0; v < graph->size; ++v) 
    { 
        struct AdjListNode* pCrawl = graph->array[v].head; 
        printf("\n %d -->", v); 
        while (pCrawl) 
        { 
            printf(" %d@%d", pCrawl->dst, pCrawl->weight); 
            pCrawl = pCrawl->next; 
        } 
        printf("\n"); 
    } 
} 

void setup(struct Graph* graph) {
    int i;
    for (i = 0; i < SIZE; i++) {  // we will fill up vertex i's out-edges
        int n = rand() % SIZE;    // how many out-edges will i have?
        while (n > 0) {
            // whom to point to? (currently allowing SELF; I may disallow later)
            // at what cost?
            addEdge(graph, i, rand() % SIZE, rand() % 100); 
            n--;
        }
    }  
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

void dijkstra (struct Graph* graph, int src, int *dist, int *prev) {
    int* pq = init(SIZE);
    int i, u, cost;
    struct AdjListNode* neighbor = NULL;
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
        neighbor = graph->array[u].head; 
        while (neighbor) { 
            i = neighbor->dst;
            cost = neighbor->weight;
            if (dist[i] > dist[u] + cost) {  // if we can improve the best-known dist from src to i
                dist[i] = dist[u] + cost;  // improve it
                prev[i] = u;  // note that we got there via 'u'
                adjustWeight(i, dist[i], pq); // and stash the improvement in the PQ
            }
            neighbor = neighbor->next; 
        }
    }
    freePQ(pq);
    return;
}

int main(int argc, const char * argv[])
{
    srand((unsigned int) time(NULL));
    int src = rand() % SIZE;
    struct Graph* graph = createGraph(SIZE); 
    setup(graph);
    printGraph(graph);
    int* prev = mallocN (SIZE * sizeof *prev);
    int* dist = mallocN (SIZE * sizeof *dist);
    dijkstra(graph, src, dist, prev);
    getPaths(src, dist, prev);
    freeN(prev);
    freeN(dist); 
    return 0; 
}