#include<stdio.h>

// CIVL has a predefined macro _CIVL
#ifdef _CIVL 
  // CIVL will make N an input variable
  // automatically
  #include <civlc.cvh>
  $input int N;
  $assume(0 < N && N < 10);
#else
  // if not runned by CIVL, 
  // then make N a macro.  
  #define N 100
#endif

int input[N];
int sum = 0;

int main(){
  for(int i = 0; i < N; i++)
    input[i] = i;
  for(int i = 0; i < N; i++)
    sum += input[i];
#ifdef _CIVL
  // assertion only added for CIVL
  $assert(sum == N*(N-1)/2);
#endif
  printf("N = %d, sum = %d\n", N, sum);
  fflush(stdout);
  return 0;
}
