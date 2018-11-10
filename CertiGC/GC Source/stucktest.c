#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <assert.h>

typedef int intnat;

typedef void  * value
  __attribute((aligned(_Alignof(void *))));

int test_int_or_ptr (value x) /* returns 1 if int, 0 if aligned ptr */ {
    return (int)(((intnat)x)&1);
}

int Is_from(value* from_start, value * from_limit,  value * v) {
    return (from_start <= v && v < from_limit);
}

int test1 () {
	value *a, *b, *c, *d, *e, *f;
	a = (value *)malloc(128 * sizeof(value));
	b = a + 50;
	c = (value *)b + 1;
	d = (intnat)83;
	e = (intnat)79;	
	printf("a was %s\n", test_int_or_ptr (a)?"int":"ptr");
	printf("b was %s\n", test_int_or_ptr (b)?"int":"ptr");
	printf("c was %s\n", test_int_or_ptr (c)?"int":"ptr");
	printf("d was %s\n", test_int_or_ptr (d)?"int":"ptr");
	printf("e was %s\n", test_int_or_ptr (e)?"int":"ptr");
	printf ("actual values:\n a: %i\n b: %i\n c: %i\n d: %i\n e: %i\n",(intnat)a,(intnat)b,(intnat)c,(intnat)d,(intnat)e);
	return 1;
}

int test2 () {
	value *from_start1 = malloc (128 * sizeof(value));
	value *junk = malloc (1000000);
	value *from_start2 = malloc (128 * sizeof(value));
	value *from_limit1 = (value*)from_start1 + 128;
	value *from_limit2 = (value*)from_start2 + 128;
    value *v1_1 = (value*) from_start1 + 20;
    value *v2_1 = (value*) v1_1 - 21;
    value *v3_1 = (value*) v2_1 + 200;
    value *v1_2 = (value*) from_start2 + 20;
    value *v2_2 = (value*) v1_2 - 21;
    value *v3_2 = (value*) v2_2 + 200;
	int ans1 = Is_from(from_start1, from_limit1, v1_1);
	int ans2 = Is_from(from_start1, from_limit1, v2_1);
	int ans3 = Is_from(from_start1, from_limit1, v3_1);
	int ans4 = Is_from(from_start1, from_limit1, v1_2);
	int ans5 = Is_from(from_start1, from_limit1, v2_2);
	int ans6 = Is_from(from_start1, from_limit1, v3_2);
	int ans7 = Is_from(from_start2, from_limit2, v1_1);
	int ans8 = Is_from(from_start2, from_limit2, v2_1);
	int ans9 = Is_from(from_start2, from_limit2, v3_1);
	int ans10 = Is_from(from_start2, from_limit2, v1_2);
	int ans11 = Is_from(from_start2, from_limit2, v2_2);
	int ans12 = Is_from(from_start2, from_limit2, v3_2);
/* yes, no, no, no*, no*, no* */
/* no*, no*, no*, yes, no, no */
	printf("double bounded results: \n");
	printf(" ans1: %i\n ans2: %i\n ans3: %i\n ans4: %i\n ans5: %i\n ans6: %i\n", ans1, ans2, ans3, ans4, ans5, ans6);
	printf(" ans7: %i\n ans8: %i\n ans9: %i\n ans10: %i\n ans11: %i\n ans12: %i\n", ans7, ans8, ans9, ans10, ans11, ans12);
	printf ("actual values:\n from_start1: %i\n from_limit1: %i\n from_start2: %i\n from_limit2: %i\n junk: %i\n ",(intnat)from_start1,(intnat)from_limit1,(intnat)from_start2,(intnat)from_limit2,(intnat)junk);
	return 1;
}

int main () {

	assert (sizeof(int) == sizeof(void *));
	test1 ();
	printf("---------------\n");
	test2 ();
	return 1;
}