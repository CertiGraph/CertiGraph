#include <stdio.h>
#include "adjacency_list.h"
#include "algos.h"

int main() {
    /* Modded from geekstogeeks
            W5 
       V0--------V1 
        |  \     | 
      W6|  W5\   |W5
        |      \ |         W1
       V2--------V3     V4-----V5
            W4
    */
    struct adjlist_graph* graph = adjlist_create_graph(6);
    adjlist_insert_edge(graph, 0, 1, 5);
    adjlist_insert_edge(graph, 0, 2, 6);
    adjlist_insert_edge(graph, 0, 3, 5);
    adjlist_insert_edge(graph, 1, 3, 5);
    adjlist_insert_edge(graph, 2, 3, 4);
    adjlist_insert_edge(graph, 4, 5, 1);
    adjlist_print(graph);
    printf("\n\n");
    struct adjlist_graph* mst0 = adjlist_prim(graph, 0);
    adjlist_print(mst0);
    printf("\n\n");
    struct adjlist_graph* mst1 = adjlist_prim(graph, 1);
    adjlist_print(mst1);
    printf("\n\n");
    struct adjlist_graph* mst5 = adjlist_prim(graph, 5);
    adjlist_print(mst5);
    printf("\n\n");
    adjlist_free_graph(mst5);
    adjlist_free_graph(mst1);
    adjlist_free_graph(mst0);
    adjlist_free_graph(graph);
    return 0;
}