//well, no need for malloc and free I guess
#include "../sample_mark/priorityqueue.h"
#include <stdio.h>

#define SIZE 8  // number of vertices
#define IFTY INT_MAX - INT_MAX/SIZE

//I feel like we should store the matrix in a struct. That way SIZE can be preserved yet it can be moved around with ease

int check_symmetric_matrix(int graph[SIZE][SIZE]) {
    for (int i = 0; i < SIZE; ++i) {
        for (int j = 0; j < i; ++j) {
            if (graph[i][j] != graph[j][i]) {
                return 0;
            }
        }
    }
    return 1;
}

void print_adj_matrix(int graph[SIZE][SIZE]) {
    for (int i = 0; i < SIZE; ++i) {
        for (int j = 0; j < SIZE; ++j) {
            if (graph[i][j] == IFTY) {
                printf("X ");
            }
            else {
                printf("%d ", graph[i][j]);
            }
        }
        printf("\n");
    }
}

void initialise_matrix(int graph[SIZE][SIZE]) {
    for (int i = 0; i < SIZE; ++i) {
        for (int j = 0; j < SIZE; ++j) {
            graph[i][j] = IFTY;
        }
    }
}

void initialise_list(int list[SIZE]) {
    for (int i = 0; i < SIZE; ++i) {
        list[i] = IFTY;
    }
}

/*
CLRS: MST-PRIM(G,w,r)
w is the weight function and stored in g, so no need
we want to return the same graph representation, so the extra parameter msf
IMPORTANT: The soundness of the graph depends on declaring evalid g (u,v) -> u <= v
    otherwise algorithm doesn't preserve whether (u,v) or (v,u) is in graph
It's not even clear in a conventional adjacency matrix anyway, because an undirected adjmatrix is symmetrical ("nice" graphs)
*/
void prim(int graph[SIZE][SIZE], int r, int msf[SIZE][SIZE]) {
    int key[SIZE];
    initialise_list(key);
    int parent[SIZE]; //NIL in textbook. However, 0 is a valid vertex, so we substitute it with an invalid value
    initialise_list(parent);
    int out[SIZE] = {0}; //as a marker to check if v is in pq. 1 for NOT in pq (already checked)
    key[r] = 0; //first in pq
    
    //Q = G.V;
    int pq[SIZE];
    for (int v = 0; v < SIZE; ++v) {
        push(v, key[v], pq);
    }
    while (!pq_emp(pq)) {
        int u = popMin(pq);
        printf("%d:", u);
        out[u] = 1;
        for (int v = 0; v < SIZE; ++v) {
            if ((!out[v]) && graph[u][v] < key[v]) {
                printf("%d ", v);
                parent[v] = u;
                key[v] = graph[u][v];
                adjustWeight(v, key[v], pq);
            }
        }
        printf("\n");
    }
    //algorithm implicitly maintains the mst A:={(v,parent[v])}
    //but it would be weird to return a different C format and call it the same graph
    //so we explicitly populate a new matrix
    //actually, a funny thing to do is to return a wedgelistgraph, then we don't have to generalize/repeat any lemmas
    for (int v = 0; v < SIZE; ++v) {
        int u = parent[v];
        int w = key[v];
        if (u != IFTY) {
            msf[u][v] = w;
            msf[v][u] = w;
        }
    }
}

int main() {
    int graph[SIZE][SIZE];
    for (int i = 0; i < SIZE; ++i) {
        for (int j = 0; j < SIZE; ++j) {
            graph[i][j] = IFTY;
        }
    }
    /* Modded from geekstogeeks
            W5 
       V0--------V1 
        |  \     | 
      W6|  W5\   |W5                          ---
        |      \ |         W1                 | |
       V2--------V3     V4-----V5     V6     V7--
            W4
    */
    graph[0][1]=5; graph[1][0]=5;
    graph[0][2]=6; graph[2][0]=6;
    graph[0][3]=5; graph[3][0]=5;
    graph[1][3]=5; graph[3][1]=5;
    graph[2][3]=4; graph[3][2]=4;
    graph[4][5]=1; graph[5][4]=1;
    graph[7][7]=1; graph[7][7]=1;
    print_adj_matrix(graph);
    int msf[SIZE][SIZE];
    for (int i = 0; i < SIZE; ++i) {
        for (int j = 0; j < SIZE; ++j) {
            msf[i][j] = IFTY;
        }
    }

    prim(graph, 0, msf);
    print_adj_matrix(msf);
    return 0;
}