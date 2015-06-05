struct Node {
  int data;
  struct Node * l;
  struct Node  * r;
};

struct Node _Alignas(8) m;

struct __attribute__((packed(4,16,1))) s2 {
          short s;          // at offset 0; byte-swap at access
          int i;            // at offset 4 (because 4-aligned); byte-swap at access
        };   

struct s2 n;
struct s2 * p;

int main()
{
  p = 0;
  p = & n;
}
