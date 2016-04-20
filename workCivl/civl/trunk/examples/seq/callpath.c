#include <assert.h>

#ifdef _CIVL

#include <civlc.cvh>

$input int x;
$input int y;

#else

int x = 1;
int y = 1;

#endif

void baz(int x) {
 assert (x == 0);
}

void foo(int x) {
  baz(x);
}

void bar(int x) {
  baz(x);
}

int main() {
  int z = 0;

  if (x > 0) z = x;
  if (y > 0) z = y;
  if (x > 0) foo(z);
  if (y > 0) bar(z);
}
