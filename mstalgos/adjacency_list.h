#ifndef __ADJACENCY_LIST_H__
#define __ADJACENCY_LIST_H__
#include "pqueue.h"

//need to alloc num_vertices, and num_vertices should not change once alloced...
struct adjlist_graph {
    int num_vertices;
    struct pqueue** edgelists;
};

struct edge {
    int u;
    int v;
    int w;
};

struct adjlist_graph* adjlist_create_graph(int num_vertices);
void adjlist_free_graph(struct adjlist_graph* graph);
void adjlist_insert_edge(struct adjlist_graph* graph, int u, int v, int weight);

void adjlist_print(struct adjlist_graph* graph);

#endif