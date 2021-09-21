//well, no need for malloc and free I guess
#include "../../priq/priq_arr.h"
#include <stdio.h>

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

void print_msf(int graph[SIZE][SIZE], int parent[SIZE]) {
    for (int i = 0; i < SIZE; ++i) {
        for (int j = 0; j < SIZE; ++j) {
            if (parent[i] == j || parent[j] == i) {
                printf("%d ", graph[i][j]);
            }
            else {
                printf("X ");
            }
        }
        printf("\n");
    }
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
int prim(int graph[SIZE][SIZE], int r, int parent[SIZE]) {
    int key[SIZE];
    initialise_list(key, IFTY);
    initialise_list(parent, SIZE);
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
            if (out[v]==0) {				//(*this is why out array is kept, to not require extra O(logn) search of pq*)
		if (graph[u][v] < key[v]) { //(*this is why key array is kept, to not require extra O(logn) search of pq*)
	                parent[v] = u;
	                key[v] = graph[u][v];
	                adjustWeight(v, key[v], pq);
		}
            }
        }
    }
    return 0;
}

int main() {
    int graph[SIZE][SIZE];
    for (int i = 0; i < SIZE; ++i) {
        for (int j = 0; j < SIZE; ++j) {
            graph[i][j] = IFTY;
        }
    }
    /*
            W5 
       V0--------V1 
        |  \     | 
      W6|  W5\   |W5                          
        |      \ |         W1                 
       V2--------V3     V4-----V5     V6     V7    V8
            W4
    */
    graph[0][1]=5; graph[1][0]=5;
    graph[0][2]=6; graph[2][0]=6;
    graph[0][3]=5; graph[3][0]=5;
    graph[1][3]=5; graph[3][1]=5;
    graph[2][3]=4; graph[3][2]=4;
    graph[4][5]=1; graph[5][4]=1;
    //graph[7][7]=1; graph[7][7]=1;
    printf("Before graph\n");
    print_adj_matrix(graph);
    printf("\n");
   int parent[SIZE] = {0};

    prim(graph, 0, parent);
    printf("Edges in forest\n");
    for (int i = 0; i < SIZE; ++i) {
        if (parent[i] < SIZE) {
            printf("%d-%d\n", i, parent[i]);
        }
    }
    printf("\n");
    printf("After Prim\n");
    print_msf(graph, parent);
    return 0;
}