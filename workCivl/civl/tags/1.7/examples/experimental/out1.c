#ifdef _CIVL
#include <civlc.cvh>
#endif

#include<stdio.h>

#ifdef _CIVL
$output int array[20];
#endif

int main() {
  FILE *fpt = fopen("output1.out","a+");
  int a[5]={1,2,3,4,5};
  
#ifdef _CIVL
  for(int i=0; i<5; i++) {
    array[i] = a[i];
  }
#else
  for(int i=0; i<5; i++) {
    fprintf(fpt,"%d\n",a[i]); 
  }
#endif
  fclose(fpt);
}


