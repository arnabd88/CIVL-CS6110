/* This example contains an error: For "incr" function, "x" is suppose
 * to be a valid pointer.
*/

#include <stdlib.h>
/*@ requires \valid(x);
  @ ensures \result == *x + 1;
  @
*/
int add(int * x) 
{
  return *x + 1;
}

/*@ 
  @ ensures *x == \result - 1;
  @*/
int incr(int * x) 
{ 
  int * y;
  int ret;

  y = (int*)malloc(sizeof(int));
  //x = y;
  ret = add(x);
  x = NULL;
  free(y);
  return ret;
}

int main() {
  incr((void *)-1);
  return 0;
}
