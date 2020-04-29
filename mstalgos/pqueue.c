/*
Wei Xiang: This is copied from VST/progs/queue.c, with changes so the queue is always sorted
Changes that affect proof:
  Major change to pqueue_put
  Obscured elem from header file, modified put and get
  Added free_pqueue
  Removed tail
  elem->next = NULL by default
A queue isn't the best implementation of a pqueue because of O(n) insert, but since the proof is largely there...
*/
#include <stddef.h>
#include "surely_malloc.h"
//#include <stdio.h>

/***********Nodes***********/

struct elem {
  int val, key;
  struct elem *next;
};

struct elem *make_elem(int val, int key) {
  struct elem *p;
  p = surely_malloc(sizeof (*p));
  p->val = val;
  p->key = key;
  p->next = NULL;
  return p;
}

void free_elem(struct elem* p) {
  maybe_free(p);
}

/***********Queue***********/

struct pqueue {
  struct elem *head;
};

struct pqueue *pqueue_new(void) {
  struct pqueue *Q = (struct pqueue *)surely_malloc(sizeof (*Q));
  Q->head = NULL;
  return Q;
}

void free_pqueue(struct pqueue* Q) {
  struct elem *m, *n;
  m = Q->head;
  n = NULL;
  while (m != NULL) {
    n = m->next;
    free_elem(m);
    m = n;
  }
  maybe_free(Q);
}

int pqueue_empty (struct pqueue *Q) {
  struct elem *h;
  h = Q->head;
  return (h == NULL);
}

//WX: Modified, needs to be reproven
void pqueue_put(struct pqueue *Q, struct elem *new) {
  struct elem *h;
  new->next=NULL;
  h = Q->head;
  //case head is nonexistent or p is smaller
  if (h==NULL || new->key < h->key) {
    Q->head = new;
    new->next = h;
  }
  else {  //case p is bigger than h
    struct elem *next, *prev;
    prev = h;
    next = h->next;
    while (next != NULL && (next->key <= new->key)) {
      prev = next;
      next = next->next;
    }
    prev->next = new;
    new->next = next;
  }
}

void pqueue_insert(struct pqueue *Q, int val, int key) {
  if (key < 0) return;  //return err?
  struct elem* n = (struct elem*) surely_malloc(sizeof(struct elem*));
  n->val = val;
  n->key = key;
  pqueue_put(Q, n);
}

struct elem *pqueue_get(struct pqueue *Q) {
  struct elem *h, *n;
  h=Q->head;
  n=h->next;
  Q->head=n;
  return h;
}

int pqueue_pop(struct pqueue *Q) {
  struct elem *h, *n;
  h=Q->head;
  n=h->next;
  Q->head=n;
  int val = h->val;
  maybe_free(h);
  return val;
}

//looks for val and returns first key if found.
int pqueue_search(struct pqueue *Q, int val) {
  struct elem *n = Q->head;
  while(n != NULL) {
    if (n->val == val) {
      return n->key;
    }
    n = n->next;
  }
  return -1;
}

//looks for val and deletes ALL instances
void pqueue_delete(struct pqueue *Q, int val) {
  struct elem *p, *n;
  p = NULL;
  n = Q->head;
  while(n != NULL) {
    if (n->val == val) {
      if (p == NULL) {  //head
        Q->head = n->next;
        free_elem(n);
        n = Q->head;
      } else {
        p->next = n->next;
        free_elem(n);
        n = p->next;
      }
    } else {
      p = n;
      n = n->next;
    }
  }
}

//looks for val; if found, delete ALL instances. Then insert new version
void pqueue_update(struct pqueue *Q, int val, int newkey) {
  if (newkey < 0) return;  //return err?
  pqueue_delete(Q, val);
  pqueue_insert(Q, val, newkey);
}

/*
void print_pqueue(struct pqueue *Q) {
  struct elem *n;
  n = Q->head;
  while (n != NULL) {
    printf("%d[%d]",n->val, n->key);
    if (n->next != NULL) {
      printf(" --> ");
    }
    n = n->next;
  }
}
*/