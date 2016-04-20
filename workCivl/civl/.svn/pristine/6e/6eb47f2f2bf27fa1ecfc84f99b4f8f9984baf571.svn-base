/* Simple test for comparing functional equivalence which have output files.
 * function: assign an array and output it.
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
  int b[5];

  for(int i=0;i<5;i++) {
    b[i] = i+1;
  }
#ifdef _CIVL
  for(int i=0; i<5; i++) {
    ARRAY[i] = b[i];
  }
#else
  for(int i=0; i<5; i++) {
    fprintf(fpt,"%d\n",b[i]); 
  }
#endif
  fclose(fpt);
}


