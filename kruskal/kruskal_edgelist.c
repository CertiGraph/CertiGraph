#include "../sample_mark/priorityqueue.h"
#include "../sample_mark/unionfind_arr.h"
//#include <malloc.h>
extern void * mallocN(int n);
extern void free(void *p);
//#include <stdio.h>

//adjacency matrices aren't good for Kruskal's, because the edge_list has to be constructed and sorted

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
    struct edge edge_list[SIZE];    //I'll change this once more when the pq is finalized
};

/*
Modified version of qsort1 from Cbench. Wanted to import a generic verified quicksort, but
-Using an array of void* pointers will lead to the casting issue. They did it from void*-to-double* in qsort4, but I'm not sure about arbitrary structures
-The CBench versions are based on doubles, and I'm worried about lifting

a is flat edge array
m is first index
n is last index
*/
void sort_edges(struct edge *a, int m, int n) {
  int i, j, pivot;
  struct edge tmp;

  if (m < n) {
    pivot = a[n].weight;
    i = m; j = n;
    while (i <= j) {
      while (a[i].weight < pivot) i++;
      while (a[j].weight > pivot) j--;
      if (i <= j) {
        tmp.u = a[i].u; tmp.v = a[i].v; tmp.weight = a[i].weight;
        a[i].u = a[j].u; a[i].v = a[j].v; a[i].weight = a[j].weight;
        a[j].u = tmp.u; a[j].v = tmp.v; a[j].weight = tmp.weight;
        i++; j--;
      }
    }
    sort_edges(a, m, j);
    sort_edges(a, i, n);
  }
}

void free_graph(struct graph * graph) {
    free(graph);
}

void kruskal(struct graph *graph, struct graph *mst) {
    int V = graph->V;
    struct subset* subsets = makeSet(V);
    
    //"sort"
    int pq[SIZE];   //better make a statement that all weights < IFTY
    for (int i = 0; i < SIZE; ++i) {
        pq[i] = IFTY;
    }
    for (int i = 0; i < graph->E; ++i) {
        int weight = graph->edge_list[i].weight;      //I believe this is invalid in verifiable C, but normalization should handle it?
        push(i, weight, pq);
    }

    while (!pq_emp(pq)) {
        int next_edge = popMin(pq);
        int u = graph->edge_list[next_edge].u;
        int v = graph->edge_list[next_edge].v;
        int ufind = find(subsets, u);
        int vfind = find(subsets, v);
        if (ufind != vfind) {
            //add edge to MST
            mst->edge_list[mst->E].u = graph->edge_list[next_edge].u;
            mst->edge_list[mst->E].v = graph->edge_list[next_edge].v;
            mst->edge_list[mst->E].weight = graph->edge_list[next_edge].weight;
            mst->E += 1;
            Union(subsets, u, v);
        }
    }
    free(subsets);
}

void kruskal_sort(struct graph * graph, struct graph * mst) {
    int V = graph->V;
    struct subset* subsets = makeSet(V);
    sort_edges(graph->edge_list, 0, graph->E);
    for (int i = 0; i < graph->E; ++i) {
        int u = graph->edge_list[i].u;      //I believe this is invalid in verifiable C, but normalization should handle it?
        int v = graph->edge_list[i].v;
        int ufind = find(subsets, u);
        int vfind = find(subsets, v);
        if (ufind != vfind) {
            //add edge to MST
            mst->edge_list[mst->E].u = graph->edge_list[i].u;
            mst->edge_list[mst->E].v = graph->edge_list[i].v;
            mst->edge_list[mst->E].weight = graph->edge_list[i].weight;
            mst->E += 1;
            Union(subsets, u, v);
        }
    }
    free(subsets);
}

/*************************RUNTIME*************************/

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
    struct graph * graph = mallocN(sizeof(struct graph ));
    graph->V =6;
    graph->E = 6;

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

//creates a graph with zero edges
struct graph * init_mst(int V) {
    struct graph * mst = mallocN(sizeof(struct graph ));
    mst->V = V;
    mst->E = 0;
    return mst;
}
/*
void print_graph(struct graph * graph) {
    printf("V: %d E: %d\n", graph->V, graph->E);
    for (int i = 0; i < graph->E; ++i) {
        printf("%d-%d %d\n", graph->edge_list[i].u, graph->edge_list[i].v, graph->edge_list[i].weight);
    }
}

int main() {
    struct graph * graph = init_graph_sample();
    print_graph(graph);
    printf("\n");
    struct graph * mst = init_mst(graph->V);
    kruskal(graph, mst);
    print_graph(mst);
    free_graph(mst);
    free_graph(graph);
    return 0;
}
*/