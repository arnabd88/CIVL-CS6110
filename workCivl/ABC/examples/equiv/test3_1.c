/*
 * test3_0.c and test3_1.c are not equivalent because 
 * they have different private list for the parallel construct.
*/

#include <omp.h>
#include <stdio.h>
#include <stdlib.h>

int main (int argc, char *argv[]) {
  
  int nthreads, tid;

  #pragma omp parallel private(nthreads)
  {
    tid = omp_get_thread_num();
    printf("Hello World from thread = %d\n", tid);
    
    if (tid == 0) {
      nthreads = omp_get_num_threads();
      printf("Number of threads = %d\n", nthreads);
    }
  }
  exit(0);
}
