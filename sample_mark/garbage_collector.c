struct HeadNode {
  int size;
  int mark; /* To reduce memory overhead, this field can be embedded into size */
  int forward;
};

struct ContendNode {
  int flag; /* 0 for pointer, 1 for data */
            /* To reduce memory overhead, this field can be embedded into pointer_or_data */
  int pointer_or_data;
};

union Node {
  struct HeadNode h;
  struct ContendNode c;
};

int heap[500000];

void mark (int x)
{
  struct HeadNode * hd;
  struct ContendNode * ct;
  int i, sz, root_mark, node_flag;
  if (x == -1)
    return;
  hd = (struct HeadNode *) (heap + x);
  root_mark = hd -> mark;
  if (root_mark == 1)
    return;
  sz = hd -> size;
  ct = (struct ContendNode *) (heap + x + sizeof(struct HeadNode));
  for (i = 0; i < sz; ++ i) {
    node_flag = (ct + i) -> flag;
    if (node_flag == 0)
      mark((ct + i) -> pointer_or_data);
  }
}

int main()
{
}

