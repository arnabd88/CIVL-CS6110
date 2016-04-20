#include <omp.h>

#define N 10

int main (int argc, char *argv[]) {
  double a[N], b[N];
  int i, sum;
  

    
// This omp construct is completely eliminated
/*
#pragma omp parallel for
    for (i=0; i < N-1; i++)
      b[i+1] = a[i+1] + 2*i;
      */
      
// These nested omp constructs are completely eliminated
{ 
    for (i=0; i < N-1; i++)
      b[i+1] = a[i+1] + 2*i;
}
      
    /*  
#pragma omp parallel for
    for (i=0; i < N; i++) {
      a[i] = 0.0;
      b[i] = a[i];
      b[i] = a[i] + b[i];
    }
    
#pragma omp parallel for
	for (i=0; i < N-1; i++)
	  a[i+1] = a[1+i] + 1;
	  //a[i+2-1] = a[(-2*3) + 2*i - i + 7] + 1;
      
      
#pragma omp parallel for private(sum)
    for (i=0; i < N; i++)
      sum = sum + i;
      
#pragma omp parallel for 
    for (i=0; i < N; i++)
      sum = sum + i;
      */
      
}
