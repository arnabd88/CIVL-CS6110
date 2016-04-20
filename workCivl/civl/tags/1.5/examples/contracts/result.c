#include<assert.h>

int gimmeOne() 
  $ensures {$result == 1} {
  return 1;
}

int main() {
  int x = gimmeOne();

  assert(x == 1);
}
