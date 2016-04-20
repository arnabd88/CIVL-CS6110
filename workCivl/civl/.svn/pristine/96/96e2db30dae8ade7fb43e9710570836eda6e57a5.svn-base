#include <assert.h>

/*@ requires \valid(x + (0 .. 3));

  @ requires \valid(x[0] + (0 .. 3));
  @ requires \valid(x[1] + (0 .. 3));
  @ requires \valid(x[2] + (0 .. 3));
*/
int add(int ** x) 
{
  int * y = x[0]+1;

  x[0][0] = 9;
  x[0][1] = 8;
  assert(x[0][0] - x[0][1] == 1);
  return 0;
}


int main() {
  add((void*)0);
  return 0;
}
