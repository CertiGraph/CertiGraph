#include <stdlib.h>
#include <limits.h>
#include <stdio.h>
#include <time.h>

#define IFTY INT_MAX
#define SIZE 8  // number of vertices
#define CONN 5  // the connectedness. 1 is 100%, higher numbers mean less connected
#define INFL 50 // increase this to inflate the highest possible cost, thus creating greater ranges


/* ****************************** */
/* Linked List Masquerading as PQ */
/* ****************************** */

struct Node { int vertex; int weight; struct Node *next; struct Node *prev;};

void push (int vertex, int weight, struct Node **list) {
    struct Node* newHead = (struct Node *) malloc (sizeof (struct Node));
    newHead->vertex = vertex;
    newHead->weight = weight;
    newHead->prev=NULL;
    newHead->next = *list;
    if (*list != NULL)
        (*list)->prev = newHead;
    *list = newHead;
}

void deleteNode (struct Node *del, struct Node **head) {
    if (*head == NULL || del == NULL) return;
    if (*head == del) *head = del->next;
    if (del->next != NULL) del->next->prev = del->prev;
    if (del->prev != NULL) del->prev->next = del->next;
    free(del);
    return;
}

int popMin (struct Node **head) {
    int minWeight = IFTY;
    int minVertex = -1;
    struct Node *minNode = NULL;
    struct Node *current = *head;
    while (current != NULL) {
        if (current->weight < minWeight) {
            minWeight = current->weight;
            minVertex = current->vertex;
            minNode = current;
        } current = current->next;
    }
    deleteNode(minNode, head);
    return minVertex;
}

void adjustWeight (int vertex, int newWeight, struct Node **head) {
    struct Node *current = *head;
    while (current != NULL) {
        if (current->vertex == vertex) {
            current->weight = newWeight;
            return;
        } current = current->next;
    }
}

void print_verts (struct Node *list) {
    if (list == NULL) printf("A blank list was provided.\n");
    struct Node *current = list;
    while (current != NULL) {
        printf ("%d\t", current->vertex);
        current = current->next;
    } printf ("\n");
}

// Used only for testing, will be removed eventually.
void print_list (struct Node *list) {
    if (list == NULL) printf("A blank list was provided.\n");
    struct Node *current = list;
    while (current != NULL) {
        printf ("(%d, %d)\t", current->vertex, current->weight);
        current = current->next;
    } printf ("\n");
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


/* ******** */
/* Solution */
/* ******** */

int dist[SIZE];
int prev[SIZE];

void dijkstra () {
    int i, u;
    struct Node *pq = NULL;
    for (i = 0; i < SIZE; i++) {
        dist[i] = (i == src) ? 0 : IFTY;  // Best-known distance from src to i
        prev[i] = IFTY;                   // Last vertex visited before i
        push(i, dist[i], &pq);            // Everybody goes in the queue
    }
    while (pq != NULL) {
        u = popMin(&pq); // this is the next candidate we will deal with (once and for all)
        if (u < 0) // The "min" actually had distance infinity. All the rest in the PQ are unreachable.
            break;
        for (i = 0; i < SIZE; i++) {
            if ((graph[u][i]) < IFTY) { // i.e. node i is a neighbor of mine
                if (dist[i] > dist[u] + graph[u][i]) { // if we can improve the best-known dist from src to i
                    dist[i] = dist[u] + graph[u][i];   // improve it
                    prev[i] = u;                       // note that we got there via 'u'
                    adjustWeight(i, dist[i], &pq);     // and then stash the improvement in the PQ
                    printf("Improved the dist to get to vertex %d to %d\n", i, dist[i]);
                    // uncomment the above line to see how the "best answer" improves slowly!
                }
            }
        }
    }
}

void getPath (int dst) {
    if (dst != src && dist[dst] < IFTY) {
        printf("Travel from %d to %d at cost %d via: ", src, dst, dist[dst]);
        struct Node *pq = NULL;
        int before; before = dst;
        while (before < IFTY) {
            push(before, 0, &pq);
            before = prev[before];
        } print_verts(pq);
    }
}

void getPaths () {
    int i;
    for (i = 0; i < SIZE; i++) {
        if (dist[i] < IFTY)
            getPath(i);
        else
            printf ("Vertex %d was unreachable altogether\n", i);
    }
}

int main(int argc, const char * argv[])
{
    setup();
    print_graph();
    dijkstra();
    getPaths();
    return 0;
}

