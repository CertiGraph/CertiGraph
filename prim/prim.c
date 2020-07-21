//well, no need for malloc and free I guess
#include "../../priq/priq_arr.h"

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

void initialise_matrix(int graph[SIZE][SIZE], int a) {
    for (int i = 0; i < SIZE; ++i) {
        for (int j = 0; j < SIZE; ++j) {
            graph[i][j] = a;
        }
    }
}

void initialise_list(int list[SIZE], int a) {
    for (int i = 0; i < SIZE; ++i) {
        list[i] = a;
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
    initialise_list(key, IFTY);
    int parent[SIZE]; //NIL in textbook. However, 0 is a valid vertex, so we substitute it with an invalid value
    initialise_list(parent, IFTY);
    int out[SIZE]; //as a marker to check if v is in pq. 1 for NOT in pq (already checked)
    initialise_list(out, 0);
    key[r] = 0; //first in pq
    
    //Q = G.V;
    int pq[SIZE];
    for (int v = 0; v < SIZE; ++v) {
        push(v, key[v], pq);
    }
    while (!pq_emp(pq)) {
        int u = popMin(pq);
        out[u] = 1;
        for (int v = 0; v < SIZE; ++v) {
            if ((!out[v]) && graph[u][v] < key[v]) {
                parent[v] = u;
                key[v] = graph[u][v];
                adjustWeight(v, key[v], pq);
            }
        }
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