all: prim kruskal

prim: test.c algos.c algos.h adjacency_list.c adjacency_list.h pqueue.c pqueue.h surely_malloc.c surely_malloc.h
	gcc -o prim surely_malloc.c pqueue.c adjacency_list.c algos.c test.c -Wall -Werror

kruskal: kruskal_edgelist.c unionfind_arr.c unionfind_arr.h surely_malloc.c surely_malloc.h
	gcc -o kruskal surely_malloc.c unionfind_arr.c kruskal_edgelist.c -Wall -Werror

clean:
	rm -f prim kruskal