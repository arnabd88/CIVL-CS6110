#include <omp.h>
#define N 10

int main (int argc, char * argv[]){
  double a[N];
  double b[N];

  foo(a,b);
}

void foo(int* a, int* b) {
#pragma omp parallel
#pragma omp for
  for(int i=0; i<N; i++)
      a[i] = b[i];
}


void fooSimplified(int* a, int* b) {
  if (a != b && a+(N-1) < b && b+(N-1) < a) {
    for(int i=0; i<N; i++)
      a[i] = b[i];
  } else {
#pragma omp parallel
#pragma omp for
    for(int i=0; i<N; i++)
      a[i] = b[i];
  }
}
