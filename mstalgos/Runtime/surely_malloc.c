#include <malloc.h>
#include <stdlib.h>

void *surely_malloc (size_t n) {
  void *p = malloc(n);
  if (!p) exit(1);
  return p;
}

//Is just a wrapper so I don't have to include malloc.h in other files
void maybe_free(void *p) {
	free(p);
}