#ifndef __UNIONFIND_ARR_H__
#define __UNIONFIND_ARR_H__

// A structure to represent a subset for union-find
struct subset
{
    int parent;
    unsigned int rank;
};
 
// A utility function to find set of an element i
// (uses path compression technique)
int find(struct subset subsets[], int i);

void Union(struct subset subsets[], int x, int y);

struct subset* makeSet(int V);

#endif