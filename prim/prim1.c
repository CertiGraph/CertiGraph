#include "../priq/priq_arr.h"

//I feel like we should store the matrix in a struct. That way size can be preserved yet it can be moved around with ease

int check_symmetric_matrix(int** graph, int size) {
    for (int i = 0; i < size; ++i) {
        for (int j = 0; j < i; ++j) {
            if (graph[i][j] != graph[j][i]) {
                return 0;
            }
        }
    }
    return 1;
}

void initialise_matrix(int** graph, int size, int a) {
    for (int i = 0; i < size; ++i) {
        for (int j = 0; j < size; ++j) {
            graph[i][j] = a;
        }
    }
}

void initialise_list(int* list, int size, int a) {
    for (int i = 0; i < size; ++i) {
        list[i] = a;
    }
}

int getCell (int** graph, int u, int i) {
    return graph[u][i];
}

/*
CLRS: MST-PRIM(G,w,r)
w is the weight function and stored in g, so no need
we want to return the same graph representation, so the extra parameter msf
IMPORTANT: The soundness of the graph depends on declaring evalid g (u,v) -> u <= v
    otherwise algorithm doesn't preserve whether (u,v) or (v,u) is in graph
It's not even clear in a conventional adjacency matrix anyway, because an undirected adjmatrix is symmetrical ("nice" graphs)
*/
void prim(int** graph, int size, int inf, int r, int* parent) {
    //This should ideally be replaced by a pq-specific "find_item_in_queue", but depending on the pq may be O(logn)
    int cost;
    int* key = mallocN (size * sizeof *key);
    initialise_list(key, size, inf);
    initialise_list(parent, size, size);
    //as a marker to check if v is in pq. 1 for NOT in pq (already checked). This should ideally be replaced by a pq-specific "in_queue"
    int* out = mallocN (size * sizeof *out);
    
    initialise_list(out, size, 0);
    key[r] = 0; //first in pq
    
    //Q = G.V;
    int* pq = init(size);
    for (int v = 0; v < size; ++v) {
        push(v, key[v], pq);
    }
    while (!pq_emp(size, inf, pq)) {
        int u = popMin(size, inf, pq);
        out[u] = 1;
        for (int v = 0; v < size; ++v) {
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
    freeN(out);
    freeN(key);
    return;
}