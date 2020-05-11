#ifndef __PRIORITYQUEUE_H___
#define __PRIORITYQUEUE_H___

//#include <limits.h>
#define INT_MAX 2147483647 //32-bit

#define SIZE 8
#define IFTY INT_MAX - INT_MAX/SIZE

void push (int vertex, int weight, int pq[SIZE]);

int popMin (int pq[SIZE]);

void adjustWeight (int vertex, int newWeight, int pq[SIZE]);

int pq_emp (int pq[SIZE]);

#endif