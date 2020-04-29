#ifndef __SURELY_MALLOC_H__
#define __SURELY_MALLOC_H__
#include <stddef.h>

void *surely_malloc (size_t n);
void maybe_free(void *p);

#endif