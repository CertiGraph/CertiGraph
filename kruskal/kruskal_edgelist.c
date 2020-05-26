#include "../sample_mark/unionfind_arr.h"

static const int MAX_EDGES = 8;

extern void * mallocK (int n);
extern void free(void *p);

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
    struct graph * empty_graph = (struct graph *) mallocK(sizeof(struct graph));
    struct edge *edge_list = (struct edge *) mallocK(sizeof(struct edge) * MAX_EDGES);
    empty_graph->V = 0;
    empty_graph->E = 0;
    empty_graph->edge_list = edge_list;
    return empty_graph;
}

/*********************SORTING***********************/
void copy_edge(struct edge *src, struct edge *dst) {
  dst->weight = src->weight;
  dst->u = src->u;
  dst->v = src->v;
}

void swap_edges(struct edge *a, struct edge *b) {
  struct edge tmp;
  tmp.weight = a->weight; tmp.u = a->u; tmp.v = a->v;
  a->weight = b->weight; a->u = b->u; a->v = b->v;
  b->weight = tmp.weight; b->u = tmp.u; b->v = tmp.v;
}

void sort_edges(struct edge* a, int m, int n) {
  int i, j;
  struct edge pivot;

  if (m < n) {
    copy_edge(a+n, &pivot);
    //pivot.weight = a[n].weight; pivot.u = a[n].u; pivot.v = a[n].v;	//copy everything to avoid headaches in proof
    i = m; j = n;
    while (i <= j) {
      while (a[i].weight < pivot.weight) i++;
      while (a[j].weight > pivot.weight) j--;
      if (i <= j) {
        if (i<j) swap_edges(a+i,a+j);
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

    sort_edges(graph->edge_list,0,graph_E-1);
    for (int i = 0; i < graph_E; ++i) {
        //extract the data

        int u = graph->edge_list[i].u;
        int v = graph->edge_list[i].v;

        //decide whether edge should be added using unionfind
        int ufind = find(subsets, u);
        int vfind = find(subsets, v);
        if (ufind != vfind) {
            //add edge to MST
            //copy_edge(graph->edge_list + i, mst->edge_list + mst->E);
            mst->edge_list[mst->E].u = u;
            mst->edge_list[mst->E].v = v;
            mst->edge_list[mst->E].weight = graph->edge_list[i].weight;
            mst->E += 1;
            Union(subsets, u, v);
        }
    }

    free(subsets);
    return mst;
}