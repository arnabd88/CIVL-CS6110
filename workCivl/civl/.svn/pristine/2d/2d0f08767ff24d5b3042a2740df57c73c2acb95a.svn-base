/* This example shows an unsatisfied assurance. */

#include <stdlib.h>
/*@ requires \valid(x);
  @ requires \valid(x[0] + (0 .. 3));
  @ ensures \result == (*(x[0]) + 2);
*/
int add(int ** x) 
{
  return *(x[0]) + 1;
}


int main() {
  add(NULL);
  return 0;
}
