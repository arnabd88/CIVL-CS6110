#include <omp.h>
#include <stdio.h>

int main (int argc, char * argv[]){
  double a[3];
  double b[3];
  double c[3];
  int zero = 0;
  int three = 3;
  int one = 1;
  int i;

#pragma omp parallel
  {
#pragma omp for
    for(i=zero; three > i; i+=one)
      a[i] = i;
  }
#pragma omp parallel
  {
#pragma omp for
    for(int j=three; j > zero; j = j - 1){
      b[three - j] = three - j;
    }
  }

#pragma omp parallel
  {
#pragma omp for
    for(int j=three; j >= one; j--){
      c[three - j] = three - j;
    }
  }
  
  //Properties checking
  for(int j = 0; j<three; j++){
    $assert a[j] == b[j];
    $assert b[j] == j;
    $assert c[j] == b[j];
  }
  return 0;
}
