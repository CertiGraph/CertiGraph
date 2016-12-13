struct Node {
    int rank;
    struct Node * parent;
};

struct Node* find(struct Node* x) {
    struct Node *p, *p0;
    p = x -> parent;
    if (p != x) {
        p0 = find(p);
        p = p0;
        x -> parent = p;
    }
    return p;
};


void unionS(struct Node* x, struct Node* y) {
    struct Node *xRoot, *yRoot;
    int xRank, yRank;
    xRoot = find(x);
    yRoot = find(y);
    if (xRoot == yRoot) {
        return;
    }
    xRank = xRoot -> rank;
    yRank = yRoot -> rank;
    if (xRank < yRank) {
        xRoot -> parent = yRoot;
    } else if (xRank > yRank) {
        yRoot -> parent = xRoot;
    } else {
        yRoot -> parent = xRoot;
        xRoot -> rank = xRank + 1;
    }
};


