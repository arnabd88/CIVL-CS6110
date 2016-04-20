#include <stdlib.h>
/*@ requires \valid(x);
  @ ensures \result == *x + 1;
  @
*/
int add(int * x) 
{
  return *x + 1;
}

/*@ requires \valid(x + (0 .. 2));
  @ ensures \valid(x + (0 .. 2));
  @ ensures x[0] + 1 == \result;
  @*/
int incr(int * x) 
{ 
  int * y;
  int ret;

  y = (int*)malloc(sizeof(int));
  ret = add(x);
  free(x);
  free(y);
  return ret;
}

int main() {
  incr((void *)-1);
  return 0;
}
