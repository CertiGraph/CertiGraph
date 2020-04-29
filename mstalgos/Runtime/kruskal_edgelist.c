#include "surely_malloc.h"
#include "unionfind_arr.h"
#include <stdio.h>

//adjacency matrices aren't good for Kruskal's, because the edge_list has to be constructed and sorted

typedef struct edge {
    int u;
    int v;
    int weight;
} edge_t;

//this haphazard representation means it's dangerous to modify a graph...
typedef struct graph {
    int V;   //represents number of vertices, assumes every 0<=n<=V is a vertex
    int E;
    edge_t* edge_list;
} graph_t;

//create a sample graph
graph_t* init_graph_sample() {
    /* Modded from geekstogeeks
            W5 
       V0--------V1 
        |  \     | 
      W6|  W5\   |W5
        |      \ |         W1
       V2--------V3     V4-----V5
            W4
    */
    graph_t* graph = surely_malloc(sizeof(graph_t));
    graph->V =6;
    graph->E = 6;
    edge_t* edge_list = surely_malloc(5*sizeof(edge_t));

    //already sorted, but todo: write an in-place sort

    // add edge 5-6
    edge_list[5].u = 5; 
    edge_list[5].v = 6; 
    edge_list[5].weight = 1;

    // add edge 2-3 
    edge_list[0].u = 2; 
    edge_list[0].v = 3; 
    edge_list[0].weight = 4;

    //the ordering of the next 3 edges will determine the MST returned

    // add edge 0-3 
    edge_list[1].u = 0; 
    edge_list[1].v = 3; 
    edge_list[1].weight = 5;

    // add edge 0-1 
    edge_list[3].u = 0; 
    edge_list[3].v = 1; 
    edge_list[3].weight = 5; 
    
    // add edge 1-3 
    edge_list[4].u = 1; 
    edge_list[4].v = 3; 
    edge_list[4].weight = 5;
    
    // add edge 0-2 
    edge_list[2].u = 0; 
    edge_list[2].v = 2; 
    edge_list[2].weight = 6;

    //sort!!

    graph->edge_list = edge_list;

    return graph;
}

//creates a graph with zero edges
graph_t* init_mst(int V) {
    graph_t* mst = surely_malloc(sizeof(graph_t));
    mst->V = V;
    mst->E = 0;
    //bit abusive, knowing that mst will never have more than V edges
    //Maybe I should standardise to maximum number of edges? V(V-1)/2
    edge_t* edge_list = surely_malloc(V*sizeof(edge_t));
    mst->edge_list = edge_list;
    return mst;
}

void free_graph(graph_t* graph) {
    maybe_free(graph->edge_list);
    maybe_free(graph);
}

void kruskal(graph_t* graph, graph_t* mst) {
    int V = graph->V;
    struct subset* subsets = makeSet(V);
    //assume edge_list already sorted by weight
    //sort_by_weight(graph->edge_list);
    for (int i = 0; i < graph->E; ++i) {
        int u = graph->edge_list[i].u;      //I believe this is invalid in verifiable C, but normalization should handle it?
        int v = graph->edge_list[i].v;
        int ufind = find(subsets, u);
        int vfind = find(subsets, v);
        //printf("Now processing %d: %d -- %d: %d\n", u, ufind, v, vfind);
        if (ufind != vfind) {
            //add edge to MST
            //printf("Added %d -- %d\n", u, v);
            mst->edge_list[mst->E] = graph->edge_list[i];   //pretty sure weird troubles will happen here. Should explicitly copy the fields over
            mst->E += 1;
            Union(subsets, u, v);
        }
    }
    freeSet(subsets);
}

void print_mst(graph_t* mst) {
    printf("V: %d E: %d\n", mst->V, mst->E);
    for (int i = 0; i < mst->E; ++i) {
        printf("%d-%d %d\n", mst->edge_list[i].u, mst->edge_list[i].v, mst->edge_list[i].weight);
    }
}

int main() {
    graph_t* graph = init_graph_sample();
    graph_t* mst = init_mst(graph->V);
    kruskal(graph, mst);
    print_mst(mst);
    free_graph(graph);
    free_graph(mst);
    return 0;
}