
#define SIZE 8

void push (int vertex, int weight, int pq[SIZE]);

int popMin (int pq[SIZE]);

void adjustWeight (int vertex, int newWeight, int pq[SIZE]);

int pq_emp (int pq[SIZE]);