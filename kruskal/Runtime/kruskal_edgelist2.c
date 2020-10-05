#include "unionfind_arr.h"
#include <malloc.h>
#include <stdio.h>

#define INT_MAX 2147483647

static const int MAX_EDGES = 8;  //don't want to use MAX_MAX_EDGES because mallocing that much is crazy

struct edge {
    int weight; //weight at top for minor convenience
    int src;
    int dst;
};

//this haphazard representation means it's dangerous to modify a graph...
//whatever, not expecting so much functionality anyway
struct graph {
    int V;   //represents number of vertices, assumes every 0<=n<=V is a vertex
    int E;
    struct edge *edge_list;    //I'll change this once more when the pq is finalized
};

//creates a graph with zero vertices and edges
struct graph * init_empty_graph() {
    struct graph * empty_graph = (struct graph *) malloc(sizeof(struct graph));
    struct edge *edge_list = (struct edge *) malloc(sizeof(struct edge) * MAX_EDGES);
    empty_graph->V = 0;
    empty_graph->E = 0;
    empty_graph->edge_list = edge_list;
    return empty_graph;
}

void fill_edge(struct edge *wedge, int w, int u, int v) {
  wedge->weight = w;
  wedge->src = u;
  wedge->dst = v;
}

void swap_edges(struct edge *a, struct edge *b) {
	struct edge tmp;
  tmp.weight = a->weight; tmp.src = a->src; tmp.dst = a->dst;
	a->weight = b->weight; a->src = b->src; a->dst = b->dst;
	b->weight = tmp.weight; b->src = tmp.src; b->dst = tmp.dst;
}

int yucky_find_min(struct edge* a, int lo, int hi) {
  int min_value = INT_MAX;
  int min_index = lo;
  for (int i = lo; i < hi; ++i) {
    int w = a[i].weight;
    if (w <= min_value) {
      min_value = w;
      min_index = i;
    }
  }
  return min_index;
}

void yucky_sort(struct edge* a, int n) {
  //selection sort
  //struct edge tmp;
  int i = 0;
  while (i <= n) {
    int j = yucky_find_min(a, i, n);
    swap_edges(a+i,a+j);
    ++i;
  }
  return;
}

void free_graph(struct graph * graph) {
    free(graph->edge_list);
    free(graph);
}

struct graph *kruskal(struct graph *graph) {
    int graph_V = graph->V;
    int graph_E = graph->E;
    struct subset *subsets = makeSet(graph_V);
    struct graph *mst = init_empty_graph();
    
    //"add" all vertices
    mst->V = graph_V;

    yucky_sort(graph->edge_list, graph_E-1);

    for (int i = 0; i < graph_E; ++i) {
        //extract the data

        int u = graph->edge_list[i].src;
        int v = graph->edge_list[i].dst;

        //decide whether edge should be added using unionfind
        int ufind = find(subsets, u);
        int vfind = find(subsets, v);
        if (ufind != vfind) {
            //add edge to MST
            int w = graph->edge_list[i].weight;
            fill_edge(mst->edge_list + mst->E, w, u, v);
            /*
            mst->edge_list[mst->E].src = u;
            mst->edge_list[mst->E].dst = v;
            mst->edge_list[mst->E].weight = graph->edge_list[i].weight;
            */
            mst->E += 1;
            Union(subsets, u, v);
        }
    }

    free(subsets);
    return mst;
}

/*************************TESTING*************************/

//create a sample graph
struct graph * init_graph_sample() {
    /* Modded from geekstogeeks
            W5 
       V0--------V1 
        |  \     | 
      W6|  W5\   |W5
        |      \ |         W1
       V2--------V3     V4-----V5
            W4
    */
    struct graph * graph = (struct graph *) malloc(sizeof(struct graph));
    graph->V =6;
    graph->E = 6;
    struct edge *edge_list = (struct edge *) malloc(sizeof(struct edge) * MAX_EDGES);
    graph->edge_list = edge_list;

    // add edge 4-5
    graph->edge_list[0].src = 4;
    graph->edge_list[0].dst = 5;
    graph->edge_list[0].weight = 1;

    // add edge 0-2 
    graph->edge_list[1].src = 0; 
    graph->edge_list[1].dst = 2; 
    graph->edge_list[1].weight = 6;        //needs sorting

    // add edge 2-3 
    graph->edge_list[2].src = 2; 
    graph->edge_list[2].dst = 3; 
    graph->edge_list[2].weight = 4;

    //the ordering of the next 3 edges will determine the MST returned

    // add edge 0-3 
    graph->edge_list[3].src = 0; 
    graph->edge_list[3].dst = 3; 
    graph->edge_list[3].weight = 5;

    // add edge 0-1 
    graph->edge_list[4].src = 0; 
    graph->edge_list[4].dst = 1; 
    graph->edge_list[4].weight = 5; 
    
    // add edge 1-3 
    graph->edge_list[5].src = 1; 
    graph->edge_list[5].dst = 3; 
    graph->edge_list[5].weight = 5;

    /* EXPECTED MST: 4-5, 2 of (0-1,0-3,1-3), 2-3
            W5 
       V0--------V1 
        |  \     | 
      W6|  W5\   |W5
        |      \ |         W1
       V2--------V3     V4-----V5
            W4
    */

    return graph;
}

void print_graph(struct graph * graph) {
    printf("V: %d E: %d\n", graph->V, graph->E);
    for (int i = 0; i < graph->E; ++i) {
        printf("%d-%d %d\n", graph->edge_list[i].src, graph->edge_list[i].dst, graph->edge_list[i].weight);
    }
    printf("\n");
}

int main() {
    struct graph * graph = init_graph_sample();
    printf("\nInitial graph\n");
    print_graph(graph);
    struct graph * mst = kruskal(graph);
    printf("\nResult graph\n");
    print_graph(mst);
    free_graph(mst);
    free_graph(graph);
    return 0;
}