#include<assert.h>

int i = 10;

int f()
{
  int $sef$0 = i;
  
  i = i + 1;
  return $sef$0;
}
int main()
{
  int y = f();
  
  assert(y == 10);
  assert(i == 11);
}
