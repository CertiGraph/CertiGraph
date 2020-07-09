#ifndef __UNIONFIND_ARR_H__
#define __UNIONFIND_ARR_H__

struct subset
{
    int parent;
    unsigned int rank;
};
 
int find(struct subset subsets[], int i);
void Union(struct subset subsets[], int x, int y);

struct subset* makeSet(int V);
void freeSet(struct subset *subsets);
#endif