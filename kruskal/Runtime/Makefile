all: kruskal

kruskal: kruskal_edgelist.c unionfind_arr.c  binary_heap.c unionfind_arr.h binary_heap.h
	gcc -o kruskal binary_heap.c unionfind_arr.c kruskal_edgelist.c -Wall -Werror

clean:
	rm -f kruskal