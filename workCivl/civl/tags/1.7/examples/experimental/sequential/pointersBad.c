/* This example contains errors:
 * For "add" function, x is suppose to be a valid pointer.
 * 
 * For "incr" function, y should be freed before return.
 */
#include <stdlib.h>
/*@ 
  @ requires val >= 0;
  @ ensures \result == val + 1;
  @
*/
int add(int * x, int val) 
{
  *x = val + 1;
  return *x;
}

/*@  requires *x >= 0;
  @  requires \valid(x);
  @  ensures *x == \result - 1;
  @  ensures \valid(x);
  @*/
int incr(int * x) 
{ 
  int * y;
  int ret;

  y = (int*)malloc(sizeof(int));
  *y = *x;
  ret = add(x, *y);
  return ret;
}

int main() {
  incr((void *)-1);
  return 0;
}
