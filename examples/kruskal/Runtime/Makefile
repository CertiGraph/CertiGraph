all: kruskal kruskal2

kruskal: kruskal_edgelist.c unionfind_arr.c unionfind_arr.h
	gcc -o kruskal unionfind_arr.c kruskal_edgelist.c -Wall -Werror

kruskal2: kruskal_edgelist2.c unionfind_arr.c unionfind_arr.h
	gcc -o kruskal2 unionfind_arr.c kruskal_edgelist2.c -Wall -Werror

clean:
	rm -f kruskal