
typedef unsigned int value;

int fiddle (value *p) {
  unsigned int sum, size, i;
  value tagword = p[-1];
  sum = tagword & 0xff;
  size = tagword >> 10;
  for (i=0; i<size; i++) {
    sum += p[i];
  }
  return sum;
}
