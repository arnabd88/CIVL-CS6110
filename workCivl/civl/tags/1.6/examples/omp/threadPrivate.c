#include <stdio.h>
#include <stdlib.h>
#include <omp.h>

int  a, b, i, tid;
float x;
int z[10];
 
#pragma omp threadprivate(a, x, z)
 
int main (int argc, char * argv[]){
 
/* Explicitly turn off dynamic threads */
  //omp_set_dynamic(0);
  //z[0] = 0;
  printf("1st Parallel Region:\n");
#pragma omp parallel private(b,tid)
  {
  tid = omp_get_thread_num();
  a = tid + 7;
  b = tid + 5;
  x = 1.1 * tid +1.0;
  z[0] = 9;
  printf("1Thread %d:   a,b,x,z= %d %d %f %d\n",tid,a,b,x,z[0]);
  }  /* end of parallel section */
 
  printf("************************************\n");
  printf("Master thread doing serial work here\n");
  printf("************************************\n");
 
  printf("2nd Parallel Region:\n");
#pragma omp parallel private(tid)
  {
  tid = omp_get_thread_num();
  printf("2Thread %d:   a,b,x,z= %d %d %f %d\n",tid,a,b,x,z[0]);
  }  /* end of parallel section */

}
