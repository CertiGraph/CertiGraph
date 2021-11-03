#include <stdlib.h>

/* demonstrate traversal of a read-only tree */

struct tree {
  unsigned int n;
  struct tree *left, *right;
};


unsigned int sum (struct tree *t) {
  if (t==NULL)
    return 0;
  else return t->n + sum(t->left) + sum (t->right);
}
