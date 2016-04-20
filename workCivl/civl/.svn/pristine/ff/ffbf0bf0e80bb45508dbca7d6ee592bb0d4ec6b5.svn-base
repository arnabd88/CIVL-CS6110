#include <omp.h>
#include <assert.h>
#define N 10

int main (int argc, char * argv[]){
  int i;
  int a[N];
  int sum = 0;

#pragma omp parallel 
{
#pragma omp barrier
  sum = 0;
#pragma omp barrier
  if (i > 0) {
#pragma omp barrier
    sum = sum + 1;
  } else {
#pragma omp barrier
    sum = N;
  }
#pragma omp barrier
  i = sum;
}

#pragma omp parallel
{
  sum = 0;
  if (i > 0) {
    sum = sum + 1;
  } else {
    sum = N;
  }
  i = sum;
}

#pragma omp parallel
{
  sum = 0;
  if (i > 0) {
#pragma omp barrier
    sum = sum + 1;
  } else {
#pragma omp barrier
    sum = N;
  }
  i = sum;
}

#pragma omp parallel
{
#pragma omp barrier
  sum = 0;
  if (i > 0) {
    sum = sum + 1;
  } else {
    sum = N;
  }
#pragma omp barrier
  i = sum;
}

#pragma omp parallel
{
  sum = 0;
#pragma omp barrier
  if (i > 0) {
    sum = sum + 1;
  } else {
#pragma omp barrier
    sum = N;
  }
#pragma omp barrier
  i = sum;
}

#pragma omp parallel
{
#pragma omp barrier
  sum = 0;
#pragma omp barrier
  if (i > 0) {
#pragma omp barrier
    sum = sum + 1;
  } else {
    sum = N;
  }
  i = sum;
}

}
