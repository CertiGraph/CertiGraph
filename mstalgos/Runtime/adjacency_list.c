//weakness of this implementation is that all v < size are always considered to be in graph, regardless of edge
//but, that's the same for adj matrices anyway...
#include <stdio.h>
#include "adjacency_list.h"
#include "surely_malloc.h"

/**************ADJACENCY GRAPH****************/
struct adjlist_graph* adjlist_create_graph(int num_vertices) {
    struct adjlist_graph* graph = (struct adjlist_graph*) surely_malloc(sizeof(struct adjlist_graph));
    struct pqueue** edgelists = (struct pqueue**) surely_malloc(sizeof(struct pqueue*)*num_vertices);
    for (int i = 0; i < num_vertices; ++i) {
        struct pqueue* edgelist = pqueue_new();
        edgelists[i] = edgelist;
    }
    graph->num_vertices = num_vertices;
    graph->edgelists = edgelists;
    return graph;
}

void adjlist_free_graph(struct adjlist_graph* graph) {
    for (int i = 0; i < graph->num_vertices; ++i) {
        struct pqueue* edgelist = graph->edgelists[i];
        free_pqueue(edgelist);
    }
    maybe_free(graph);
}

void adjlist_insert_edge(struct adjlist_graph* graph, int u, int v, int weight) {
    struct pqueue* edgelist;
    edgelist = graph->edgelists[u];
    pqueue_insert(edgelist, v, weight);
    edgelist = graph->edgelists[v];
    pqueue_insert(edgelist, u, weight);
}

void adjlist_print(struct adjlist_graph* graph) {
    for (int i = 0; i < graph->num_vertices; ++i) {
        printf("%d: ", i);
        struct pqueue* edgelist = graph->edgelists[i];
        print_pqueue(edgelist);
        printf("\n");
    }
}