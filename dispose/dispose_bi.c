#include <stdlib.h>

struct Node {
    int m;
    struct Node * l;
    struct Node * r;
};

void mark(struct Node * x) {
    struct Node * l, * r;
    int root_mark;
    l = x -> l;
    r = x -> r;
    x -> m = 1;
    if (l) {
        root_mark = l -> m;
        if (!root_mark) {
            mark(l);
        }
    }
    if (r) {
        root_mark = r -> m;
        if (!root_mark) {
            mark(r);
        }
    }
}

void spanning(struct Node * x) {
    struct Node * l, * r;
    int root_mark;
    l = x -> l;
    r = x -> r;
    x -> m = 1;
    if (l) {
        root_mark = l -> m;
        if (root_mark == 0) {
            spanning(l);
        } else {
            x -> l = 0;
        }
    }
    if (r) {
        root_mark = r -> m;
        if (root_mark == 0) {
            spanning(r);
        } else {
            x -> r = 0;
        }
    }
}

void dispose(struct Node * x) {
    struct Node *l, *r;
    l = x -> l;
    r = x -> r;
    if (l) {
        dispose(l);
    }
    if (r) {
        dispose(r);
    }
    free(x);
}

int main() {
    return 0;
}
