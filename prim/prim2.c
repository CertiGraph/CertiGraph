#include "../priq/priq_arr.h"

#define SIZE 8
#define INF 2147483646 // INT_MAX - 1
#define graph(i, j) (graph[(i) * SIZE + (j)])

//I feel like we should store the matrix in a struct. That way SIZE can be preserved yet it can be moved around with ease

int check_symmetric_matrix(int graph[SIZE*SIZE]) {
    for (int i = 0; i < SIZE; ++i) {
        for (int j = 0; j < i; ++j) {
            if (graph(i,j) != graph(j,i)) {
                return 0;
            }
        }
    }
    return 1;
}

//never used?
void initialise_matrix(int graph[SIZE*SIZE], int a) {
    for (int i = 0; i < SIZE*SIZE; ++i) {
        graph[i] = a;
    }
}

void initialise_list(int list[SIZE], int a) {
    for (int i = 0; i < SIZE; ++i) {
        list[i] = a;
    }
}

int getCell (int graph[SIZE*SIZE], int u, int i) {
    return graph(u,i);
}

/*
CLRS: MST-PRIM(G,w,r)
w is the weight function and stored in g, so no need
we want to return the same graph representation, so the extra parameter msf
IMPORTANT: The soundness of the graph depends on declaring evalid g (u,v) -> u <= v
    otherwise algorithm doesn't preserve whether (u,v) or (v,u) is in graph
It's not even clear in a conventional adjacency matrix anyway, because an undirected adjmatrix is symmetrical ("nice" graphs)
*/
void prim(int graph[SIZE*SIZE], int r, int parent[SIZE]) {
    //This should ideally be replaced by a pq-specific "find_item_in_queue", but depending on the pq may be O(logn)
    int cost;
    int key[SIZE];
    initialise_list(key, INF);
    initialise_list(parent, SIZE);
    //as a marker to check if v is in pq. 1 for NOT in pq (already checked). This should ideally be replaced by a pq-specific "in_queue"
    int out[SIZE];
    initialise_list(out, 0);
    key[r] = 0; //first in pq
    
    //Q = G.V;
    int* pq = init(SIZE);
    for (int v = 0; v < SIZE; ++v) {
        push(v, key[v], pq);
    }
    while (!pq_emp(SIZE, INF, pq)) {
        int u = popMin(SIZE, INF, pq);
        out[u] = 1;
        for (int v = 0; v < SIZE; ++v) {
            if (out[v]==0) {				//(*this is why out array is kept, to not require extra O(logn) search of pq*)
		        cost = getCell(graph, u, v);
                if (cost < key[v]) { //(*this is why key array is kept, to not require extra O(logn) search of pq*)
	                parent[v] = u;
	                key[v] = cost;
	                adjustWeight(v, key[v], pq);
		        }
            }
        }
    }
    freePQ(pq);
    return;
}