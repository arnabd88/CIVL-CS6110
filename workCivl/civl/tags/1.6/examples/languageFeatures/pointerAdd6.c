#include <assert.h>

int main(int argc, char * argv[]) {
  int a = 8;
  void *p = &a + 1;
  void * q = p + 0;

  return 0;
}
