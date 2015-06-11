struct __NODE {
  int m;
  struct __NODE _Alignas(16) * l;
  struct __NODE _Alignas(16) * r;
};

void mark(struct __NODE * x) {
  struct __NODE _Alignas(16) * l, * r;
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

struct __NODE _Alignas(16) * hd;
struct __NODE _Alignas(16) n;

int main()
{
  hd = & n;
  n.m = 0;
  n.l = hd;
  n.r = 0;
  mark(hd);
}
