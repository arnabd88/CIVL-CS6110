#include <assert.h>

#ifdef _CIVL

#include <civlc.cvh>

$input int x;

#else

int x = 1;

#endif

int main() {
  int y = 1;

  if (x > 0) {
    y = 0;
  }

  if (x > 0) {
    assert (y != 0);
  }
}
