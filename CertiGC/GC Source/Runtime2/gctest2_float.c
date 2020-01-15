#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include <assert.h>
#include "values.h"
#include "gc.h"

/*
Floats instead of ints.
Instead of storing the int inside the Field of the alloced node:
For each randomised float, create a new field (double precision, so two Fields)
Store ptr to it
*/

value *alloc, *limit;

#define Null ((value)1)

#define NARGS 100
value args[NARGS];

#define cons1(p,c,a0) \
  (p=(value)(allocx+1),	    \
    allocx+=2,\
    ((value*)p)[-1] = ((1<<10)|c),\
   ((value*)p)[0] = a0)

//for noscan, cons1(p, 253, a0)

#define cons2(p,c,a0,a1) \
  (p=(value)(allocx+1),	    \
    allocx+=3,\
    ((value*)p)[-1] = ((2<<10)|c),\
    ((value*)p)[0] = a0,\
    ((value*)p)[1] = a1)

#define cons3(p,c,a0,a1,a2) \
  (p=(value)(allocx+1),	    \
    allocx+=4,\
    ((value*)p)[-1] = ((3<<10)|c),\
    ((value*)p)[0] = a0,\
    ((value*)p)[1] = a1,\
    ((value*)p)[2] = a2)

#define cons4(p,c,a0,a1,a2,a3)\
  (p=(value)(allocx+1),	    \
    allocx+=5,\
    ((value*)p)[-1] = ((4<<10)|c),\
    ((value*)p)[0] = a0,\
    ((value*)p)[1] = a1,\
    ((value*)p)[2] = a2,\
    ((value*)p)[3] = a3)

#define cons5(p,c,a0,a1,a2,a3,a4)\
  (p=(value)(allocx+1),	    \
    allocx+=6,\
    ((value*)p)[-1] = ((5<<10)|c),\
    ((value*)p)[0] = a0,\
    ((value*)p)[1] = a1,\
    ((value*)p)[2] = a2,\
    ((value*)p)[3] = a3,\
    ((value*)p)[4] = a4)

typedef void (*function)(value*,value,value,value,value);
typedef void (*function0)();

#define jump(f) (((function)f)(allocx,a1,a2,a3,a4))

struct thread_info tinfo = {args,NARGS,&alloc, &limit, NULL};

#define check(fi) \
  {if (limit-allocx < fi[0]) { \
      alloc=allocx; \
      args[1]=a1; args[2]=a2; args[3]=a3; args[4]=a4; \
      garbage_collect(fi,&tinfo); \
      allocx=alloc; \
      a1=args[1]; a2=args[2]; a3=args[3]; a4=args[4]; \
    }}

void build(void);

void insert      (value *allocx, value a1, value a2, value a3, value a4) __attribute__ ((noinline));
void insert_left (value *allocx, value a1, value a2, value a3, value a4) __attribute__ ((noinline));
void insert_right(value *allocx, value a1, value a2, value a3, value a4) __attribute__ ((noinline));
void buildx      (value *allocx, value a1, value a2, value a3, value a4) __attribute__ ((noinline));
void done        (void) __attribute__ ((noinline));

//Warning! I'm on a 64-bit machine, so a sizeof(double) == sizeof(value)
const uintnat fi_cons_double [] = {2,1,1};

//returns pointer to created float object, but casted to value
//a1's the pointer to root of tree
value cons_double(value **allocx, value* a1, double f) {
  if (limit-*allocx < fi_cons_double[0]) {
    alloc=*allocx;
    args[1]=*a1;
    garbage_collect(fi_cons_double,&tinfo);
    *allocx=alloc;
    *a1=args[1];
  }
  value* fptr= *allocx;
  *allocx+=2;
  fptr[0] = ((1<<10)|253);
  ((double*)fptr)[1] = f;
  return (value) (fptr+1);
}

const uintnat fi_insert [] = {5,4,1,2,3,4};

void insert(value *allocx, value a1, value a2, value a3, value a4) {
  value t, keyptr, contf, conte;
  check(fi_insert);
  t=a1;
  keyptr = a2;
  contf=a3;
  conte=a4;
  if (t==Null) {
    value u;
    cons3(u,0,keyptr,Null,Null);
    a4=conte;
    a1=u;
    jump(contf);
  } else {
    value kptr = Field(t,0);
    value left = Field(t,1);
    value right = Field(t,2);
    double k = *((double*)kptr);
    double key = *((double*)keyptr);
    //printf("%f %f\n", k, key);
    if (key<k) {
      value e;
      cons4(e,1,kptr,right,contf,conte);
      a1=left;
      a2=keyptr;
      a3= (value)insert_left;
      a4=e;
      jump(insert);
    } else if (key>k) {
      value e;
      cons4(e,2,kptr,left,contf,conte);
      a1=right;
      a2=keyptr;
      a3= (value)insert_right;
      a4=e;
      jump(insert);
    } else {
      a4=conte;
      a1=t;
      jump(contf);
    }
  }
}

const uintnat fi_insert_left [] = {4,2,4,1};

//here, a2 is keyptr to floating obj in heap
void insert_left(value *allocx, value a1, value a2, value a3, value a4) {
  value k, e, t, u, right, contf, conte;
  check (fi_insert_left);
  e=a4;
  u=a1;
  k=Field(e,0);
  right=Field(e,1);
  contf=Field(e,2);
  conte=Field(e,3);
  cons3(t,0,k,u,right);
  a4=conte;
  a1=t;
  jump(contf);
}

const uintnat fi_insert_right [] = {4,2,4,1};

void insert_right(value *allocx, value a1, value a2, value a3, value a4) {
  value k, e, u, t, left, contf, conte;
  check (fi_insert_right);
  e=a4;
  u=a1;
  k=Field(e,0);
  left=Field(e,1);
  contf=Field(e,2);
  conte=Field(e,3);
  cons3(t,0,k,left,u);
  a4=conte;
  a1=t;
  jump(contf);
}
/*
void print_tree (value t) {
  if (Is_long(t))
    return;
  else {
    printf("%x %f\n", t, *((double*)Field(t,0)));
    print_tree(Field(t,1));
    print_tree(Field(t,2));
  }
}
*/
const uintnat fi_buildx [] = {0,2,4,1};

void buildx(value *allocx, value a1, value a2, value a3, value a4) {
  value n,t;
  check(fi_buildx);  
  n=a4;
  t=a1;
  {value n1 = Long_val(n);
  if (n1>0) {
    //double k = n1 + 0.1;
    double k = (double)random()/(double)(RAND_MAX/1000);
    value fptr = cons_double(&allocx, &a1, k);
    n1 = Val_long (n1-1);
    a2 = fptr;
    a3= (value)buildx;
    a4=n1;
    jump(insert);
  } else {
    a1=t;
    alloc=allocx;
    args[1]=a1;
    //print_tree(t);
    done();
  }
}}

void build(void) {
  buildx(alloc, args[1], args[2], args[3], args[4]);
}