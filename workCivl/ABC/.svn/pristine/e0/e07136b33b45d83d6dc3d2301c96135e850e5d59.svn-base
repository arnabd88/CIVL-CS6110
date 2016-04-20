// inner_func.c: example with inner function declaration.
// in C, the function entity should have "internal" linkage,
// so the inner declaration refers to the same function defined
// externally.
#include <assert.h>
int f(void);

int main() {
  int f(void);
  int x = f();
  
  assert(x==10);
}

int f() {
  return 10;
}
