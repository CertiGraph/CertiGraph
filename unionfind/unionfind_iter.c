struct Node {
    int rank;
    struct Node * parent;
};

struct Node* find(struct Node* x) {
    struct Node *tmp, *p;
    tmp = x;
    p = tmp -> parent;
    while (tmp != p) {
        tmp = p;
        p = tmp -> parent;
    }
    while (x != p) {
        tmp = x -> parent;
        x -> parent = p;
        x = tmp;
    }
    return p;
};
