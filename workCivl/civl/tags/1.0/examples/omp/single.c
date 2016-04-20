#include <omp.h>
#define N 10

int main (int argc, char * argv[]){
  double a[N];
  int i;

#pragma omp parallel
//#pragma omp single private(i)
if (omp_get_thread_num() == 0)
{
  int i;
  for(i=0; i<N; i++)
      a[i] = 0;
}

}
