/* Simple test for comparing functional equivalence which have output files.
 * function: initialize an array and output it.
 */

#ifdef _CIVL
#include <civlc.cvh>
#endif

#include<stdio.h>

#ifdef _CIVL
$output int ARRAY[20];
#endif

int main() {
  FILE *fpt = fopen("output","a");
  int a[5]={1,2,3,4,5};
  
#ifdef _CIVL
  for(int i=0; i<5; i++) {
    ARRAY[i] = a[i];
  }
#else
  for(int i=0; i<5; i++) {
    fprintf(fpt,"%d\n",a[i]); 
  }
#endif
  fclose(fpt);
}


