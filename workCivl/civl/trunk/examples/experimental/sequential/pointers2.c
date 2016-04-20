#include <stdlib.h>
/*@ requires \valid(x);
  @ requires *x >= 0;
  @ ensures \result == *x + 1;
  @
*/
int add(int * x) 
{
  return *x + 1;
}

/*@ requires \valid(x + (0 .. 2));
  @ requires x[1] >= 0;
  @ ensures x[1] == \result - 1;
  @ ensures \valid(x + (0 .. 2));
  @*/
int incr(int * x) 
{ 
  int * y;
  int ret;

  y = (int*)malloc(sizeof(int));
  *y = x[1];
  ret = add(&x[1]);
  free(y);
  return ret;
}

int main() {
  incr((void *)-1);
  return 0;
}
