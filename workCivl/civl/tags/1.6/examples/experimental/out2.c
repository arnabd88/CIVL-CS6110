#ifdef _CIVL
#include <civlc.cvh>
#endif

#include<stdio.h>

#ifdef _CIVL
$output int array[20];
#endif

int main() {
  FILE *fpt = fopen("output2.out","a+");
  int b[5];

  for(int i=0;i<5;i++) {
    b[i] = i+1;
  }
#ifdef _CIVL
  for(int i=0; i<5; i++) {
    array[i] = b[i];
  }
#else
  for(int i=0; i<5; i++) {
    fprintf(fpt,"%d\n",b[i]); 
  }
#endif
  fclose(fpt);
}


