extern void * mallocN (int n);

struct Node {
  struct Node * _Alignas(16) m;
  struct Node * _Alignas(8) l;
  struct Node * r;
};

struct Node * copy(struct Node * x) {
  struct Node * l, * r, * x0, * l0, * r0;
  if (x == 0)
    return 0;
  x0 = x -> m;
  if (x0 != 0)
    return x0;
  x0 = (struct Node *) mallocN (sizeof (struct Node));
  l = x -> l;
  r = x -> r;
  x -> m = x0;
  x0 -> m = 0;
  l0 = copy(l);
  x0 -> l = l0;
  r0 = copy(r);
  x0 -> r = r0;
  return x0;
}

struct Node n;

int main()
{
  struct Node * x, * y;
  x = & n;
  n.m = 0;
  n.l = & n;
  n.r = 0;
  y = copy(x);
}
