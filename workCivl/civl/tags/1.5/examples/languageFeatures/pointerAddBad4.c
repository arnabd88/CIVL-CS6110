#include <assert.h>

int main(int argc, char * argv[]) {
  int a[2][2][2] = {{{0,1}, {2,3}}, {{4,5}, {6,7}}};
  void *p = (&a + 1);
  int t;

  t = *((int*)p);
  assert(t == 1);
  return 0;
}
