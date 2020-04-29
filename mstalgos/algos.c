#include "surely_malloc.h"
//#include <limits.h>       //can't clightgen this...?
#include "pqueue.h"
#include "adjacency_list.h"
#include "unionfind_arr.h"

#define INT_MAX 2147483647  //32bit

struct adjlist_graph* adjlist_prim(struct adjlist_graph* graph, int root) {
    int num_vertices = graph->num_vertices;
    int* parents = (int*) surely_malloc(sizeof(int) * num_vertices);
    //this is just for easy reference later. extract-min still requires a pqueue
    int* keys = (int*) surely_malloc(sizeof(int) * num_vertices);
    for (int i = 0; i < num_vertices; ++i) {
        parents[i] = -1;    //hack!! but should not matter
        keys[i] = INT_MAX;
    }
    keys[root] = 0;
    struct pqueue* pqueue = pqueue_new();
    for (int i = 0; i < num_vertices; ++i) {
        pqueue_insert(pqueue, i, keys[i]);
    }
    while (!pqueue_empty(pqueue)) {
        int u = pqueue_pop(pqueue);
        struct pqueue *edgelist = graph->edgelists[u];
        //hm, had to expose struct elem for this... I guess pqueue isn't the best for edgelist
        struct elem* node = edgelist->head;
        while (node != NULL) {
            int v = node->val;
            int w = node->key;
            int v_key = pqueue_search(pqueue, v);
            if (0 <= v_key) {
                if (w < v_key) {
                    parents[v] = u;
                    keys[v] = w;
                    //BUG HERE
                    pqueue_update(pqueue,v,w);
                }
            }
            node = node->next;
        }
    }

    //finally, create mst
    struct adjlist_graph* mst = adjlist_create_graph(num_vertices);
    for (int i = 0; i < num_vertices; ++i) {
        int j = parents[i];
        if (0 <= j) {
            adjlist_insert_edge(mst,i,j,keys[i]);
        }
    }
    free_pqueue(pqueue);
    maybe_free(keys);
    maybe_free(parents);
    return mst;
}