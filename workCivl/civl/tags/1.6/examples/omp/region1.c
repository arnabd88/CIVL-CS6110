#include <omp.h>
#include <assert.h>
#define N 10

int main (int argc, char * argv[]){
  int i;
  int a[N];
  int sum = 0;

#pragma omp parallel 
{
  int max = N;

#pragma omp for
  for(i=0; i<max; i++)
      a[i] = 0;

  max = 0;
}

#pragma omp parallel
if (i>0) {
  sum = N;
} else {
  #pragma omp for reduction(+:sum)
  for(i=0; i<N; i++)
      sum = sum + a[i];
}

{
int counter = 0;
#pragma omp parallel
if (counter == 0) counter++;

assert(counter == 1);
}

}
