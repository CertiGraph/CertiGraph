//#include "binary_heap.h"
#include "unionfind_arr.h"
#include <malloc.h>
//extern void * mallocN(int n);
//extern void free(void *p);
#include <stdio.h>

static const int SIZE = 8;  //don't want to use MAX_SIZE because mallocing that much is crazy

struct edge {
    int weight; //weight at top for minor convenience
    int u;
    int v;
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
    struct edge *edge_list = (struct edge *) malloc(sizeof(struct edge) * SIZE);
    empty_graph->V = 0;
    empty_graph->E = 0;
    empty_graph->edge_list = edge_list;
    return empty_graph;
}

void swap_edges(struct edge *a, struct edge *b) {
	struct edge tmp;
        tmp.weight = a->weight; tmp.u = a->u; tmp.v = a->v;
	a->weight = b->weight; a->u = b->u; a->v = b->v;
	b->weight = tmp.weight; b->u = tmp.u; b->v = tmp.v;
}

void
sort_edges(struct edge* a, int m, int n)
{
  int i, j;
  struct edge pivot;

  if (m < n) {
    pivot.weight = a[n].weight; pivot.u = a[n].u; pivot.v = a[n].v;	//copy everything to avoid headaches in proof
    i = m; j = n;
    while (i <= j) {
      while (a[i].weight < pivot.weight) i++;
      while (a[j].weight > pivot.weight) j--;
      if (i <= j) {
	swap_edges(a+i,a+j);
        i++; j--;
      }
    }
    sort_edges(a, m, j);
    sort_edges(a, i, n);
  }
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
printf("Sorting...\n");
    sort_edges(graph->edge_list,0,graph_E-1);
printf("Sorted\n");
    for (int i = 0; i < graph_E; ++i) {
        //extract the data

        int u = graph->edge_list[i].u;
        int v = graph->edge_list[i].v;

        //decide whether edge should be added using unionfind
        int ufind = find(subsets, u);
        int vfind = find(subsets, v);
        if (ufind != vfind) {
            //add edge to MST
            mst->edge_list[mst->E].u = u;
            mst->edge_list[mst->E].v = v;
            mst->edge_list[mst->E].weight = graph->edge_list[i].weight;
            //printf("Added\n");
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
    struct edge *edge_list = (struct edge *) malloc(sizeof(struct edge) * SIZE);
    graph->edge_list = edge_list;

    // add edge 4-5
    graph->edge_list[0].u = 4;
    graph->edge_list[0].v = 5;
    graph->edge_list[0].weight = 1;

    // add edge 0-2 
    graph->edge_list[1].u = 0; 
    graph->edge_list[1].v = 2; 
    graph->edge_list[1].weight = 6;        //needs sorting

    // add edge 2-3 
    graph->edge_list[2].u = 2; 
    graph->edge_list[2].v = 3; 
    graph->edge_list[2].weight = 4;

    //the ordering of the next 3 edges will determine the MST returned

    // add edge 0-3 
    graph->edge_list[3].u = 0; 
    graph->edge_list[3].v = 3; 
    graph->edge_list[3].weight = 5;

    // add edge 0-1 
    graph->edge_list[4].u = 0; 
    graph->edge_list[4].v = 1; 
    graph->edge_list[4].weight = 5; 
    
    // add edge 1-3 
    graph->edge_list[5].u = 1; 
    graph->edge_list[5].v = 3; 
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
        printf("%d-%d %d\n", graph->edge_list[i].u, graph->edge_list[i].v, graph->edge_list[i].weight);
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