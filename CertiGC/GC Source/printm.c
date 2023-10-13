#include <stdio.h>
int main (void) {
  printf("#define SIZEOF_PTR %d\n#define SIZEOF_LONG %d\n#define SIZEOF_INT %d\n",
	 sizeof(void*), sizeof(long), sizeof(int));
  return 0;
}
