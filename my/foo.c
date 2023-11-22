#include<stdlib.h>
#include<stdio.h>

int GLOBAL = 10;

int int_id(int a) {
  return a;
}

/*
  Arguments
   - nodes: 1-D array with size of n
   - edges: 2-D array with size of m x 2
  Return
   - priority: 1-D array with size of n
*/
int *prioritizer(int *nodes, int n, int **edges, int m) {
  int *priority = (int *) calloc(n, sizeof(int));

  GLOBAL += 1;

  /* Update priority array */

  // TODO: replace with implementation of prioritizer
  // For now, I simply output the reverse of nodes
  for (int i = n-1; i >= 0 ; i--) {
    priority[i] = GLOBAL + i;
  }

  return priority;
}
