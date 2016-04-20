#include <omp.h>
#include <stdio.h>

int main () {
  int x;
  #pragma omp parallel num_threads(8)
  {
    int num = omp_get_thread_num();
    if (num > 2) {
      #pragma omp for
      for (int i=0; i<5; i++) {
        printf("In loop thread %d printing %d\n", num, i);
      } 
    } else {
      printf("Outside of loop printing %d\n", num);
    }
  }
}
