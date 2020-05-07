all: kruskal

kruskal: kruskal_edgelist.c unionfind_arr.c  priorityqueue.c unionfind_arr.h priorityqueue.h
	gcc -o kruskal priorityqueue.c unionfind_arr.c kruskal_edgelist.c -Wall -Werror

clean:
	rm -f kruskal