#include "../unionfind/unionfind_arr.h"

static const int MAX_EDGES = 8;

extern void * mallocK (int n);
extern void free (void *p);

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
    struct graph * empty_graph = (struct graph *) mallocK(sizeof(struct graph));
    struct edge *edge_list = (struct edge *) mallocK(sizeof(struct edge) * MAX_EDGES);
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

/*********************SORTING***********************/
extern void sort_edges(struct edge* a, int l);

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

    sort_edges(graph->edge_list, graph_E); //because the new sort_spec now gives the length of the list instead of the index of the last element
    
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

    freeSet(subsets);
    return mst;
}