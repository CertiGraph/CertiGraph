#define INT_MAX 2147483647
#define SIZE 8
#define IFTY INT_MAX - 1

void push (int vertex, int weight, int pq[SIZE]);

int popMin (int pq[SIZE]);

void adjustWeight (int vertex, int newWeight, int pq[SIZE]);

int pq_emp (int pq[SIZE]);