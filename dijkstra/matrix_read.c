
int getCell (int **graph, int u, int i) {
    return graph[u][i];
}

/* 
 * generated .v with 
 *   ../../CompCert/clightgen -DCOMPCERT -normalize -isystem . matrix_read.c
 */

/* 
 *  file locations on my machine:
 *
 *  |- CertiGraph/
 * 	|   |- dijkstra/
 *  |	|   |- matrix_read.c
 *  |	|   |- matrix_read.v
 *  |	|   |- verif_matrix_read.v
 *  |
 *  |- VST/
 *	|	|- ...
 *  |
 *  |- CompCert/
 *  |   |- clightgen
 *  |   |- ...
 *
 */