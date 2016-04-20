#include <omp.h>
#define N 10

int main (int argc, char * argv[]){
  double a[N], b[N], c[N];
  int i;
  
    for(i=0; i<N; i++)
      a[i] = 0;
      
    for(i=0; i<N; i++)
      b[i] = 0;
      
    for(i=0; i<N; i++)
      c[i] = 0;

#pragma omp parallel
#pragma omp for
for(int i = 0; i < N ; i ++)
a[i] = b[i] + c[i];


}
