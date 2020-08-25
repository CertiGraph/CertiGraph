#include <stddef.h>

unsigned summatrix(unsigned a[2][2], int n) {
  int i; int j; unsigned s;
  i=0;
  j=0;
  s=0;
  while (i<n) {
    j = 0; 
    while (j<n) {
      s+=a[i][j];
      j++;
    }
    i++;
  }
  return s;
}

unsigned twobytwo[2][2] = {{1,2},{3,4}};

int main(void) {
  unsigned int s;
  s = summatrix(twobytwo,2);
  return (int)s;
}

