
int* init (int size);

void push (int vertex, int weight, int* pq);

int popMin (int size, int inf, int* pq);

void adjustWeight (int vertex, int newWeight, int* pq);

int pq_emp (int size, int inf, int* pq);

void freePQ (void* pq);