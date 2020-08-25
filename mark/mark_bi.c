struct Node {
  int  _Alignas(16) m;
  struct Node * _Alignas(8) l;
  struct Node * r;
};

void mark(struct Node * x) {
  struct Node * l, * r;
  int root_mark;
  if (x == 0)
    return;
  root_mark = x -> m;
  if (root_mark == 1)
    return;
  l = x -> l;
  r = x -> r;
  x -> m = 1;
  mark(l);
  mark(r);
}

struct Node * hd;
struct Node n;

int main()
{
  hd = & n;
  n.m = 0;
  n.l = hd;
  n.r = 0;
  mark(hd);
}
