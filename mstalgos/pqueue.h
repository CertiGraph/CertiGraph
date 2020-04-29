#ifndef __PQUEUE_H__
#define __PQUEUE_H__

/***********Nodes***********/
struct elem {
  int val, key;
  struct elem *next;
};

struct elem *make_elem(int val, int key);
void free_elem(struct elem* p);


/***********Queue***********/

//key must never be negative!

struct pqueue {
  struct elem *head;
};

struct pqueue *pqueue_new(void);
void free_pqueue(struct pqueue* Q);

int pqueue_empty (struct pqueue *Q);

void pqueue_insert(struct pqueue *Q, int val, int key);
int pqueue_pop(struct pqueue *Q);

//looks for val and returns key if found
int pqueue_search(struct pqueue *Q, int val);

void pqueue_delete(struct pqueue *Q, int val);

//looks for val; if found, delete it. Then insert new version
void pqueue_update(struct pqueue *Q, int val, int newkey);

void print_pqueue(struct pqueue *Q);
#endif