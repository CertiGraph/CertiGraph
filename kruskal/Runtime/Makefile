all: kruskal

kruskal: kruskal_edgelist.c unionfind_arr.c unionfind_arr.h
	gcc -o kruskal unionfind_arr.c kruskal_edgelist.c -Wall -Werror

clean:
	rm -f kruskal