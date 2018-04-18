extern void * mallocN (int n);

// A structure to represent a subset for union-find
struct subset
{
    int parent;
    unsigned int rank;
};
 
// A utility function to find set of an element i
// (uses path compression technique)
int find(struct subset subsets[], int i)
{
    // find root and make root as parent of i (path compression)
    int p0 = 0;
    int p = subsets[i].parent;
    if (p != i) {
        p0 = find(subsets, p);
        p = p0;
        subsets[i].parent = p;
    }
 
    return p;
}

void Union(struct subset subsets[], int x, int y)
{
    int xroot, yroot;
    unsigned int xRank, yRank;

    xroot = find(subsets, x);
    yroot = find(subsets, y);
 
    if (xroot == yroot) {
        return;
    }

    xRank = subsets[xroot].rank;
    yRank = subsets[yroot].rank;
 
    // Attach smaller rank tree under root of high rank tree
    // (Union by Rank)
    if (xRank < yRank)
        subsets[xroot].parent = yroot;
    else if (xRank > yRank)
        subsets[yroot].parent = xroot;
 
    // If ranks are same, then make one as root and increment
    // its rank by one
    else
    {
        subsets[yroot].parent = xroot;
        subsets[xroot].rank = xRank + 1;
    }
}

struct subset* makeSet(int V)
{
        // Allocate memory for creating V ssubsets
    struct subset *subsets =
        (struct subset*) mallocN( V * sizeof(struct subset) );
 
    // Create V subsets with single elements
    for (int v = 0; v < V; v++)
    {
        subsets[v].parent = v;
        subsets[v].rank = 0;
    }

    return subsets;
}
