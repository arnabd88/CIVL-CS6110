#include <stdlib.h>
/*@ requires \valid(x);
  @ ensures \result == *x + 1;
  @
*/
int add(int * x) 
{
  return *x + 1;
}

/*@ requires \valid(x);
  @ requires *x >= 0;
  @ ensures *x == \result - 1;
  @*/
int incr(int * x) 
{ 
  int * y;
  int ret;

  y = (int*)malloc(sizeof(int));
  ret = add(x);
  free(y);
  return ret;
}

int main() {
  incr((void *)-1);
  return 0;
}
