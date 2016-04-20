#include <assert.h>

#ifdef _CIVL

#include <civlc.cvh>

$input int x;
$input int y;

#else

int x = 1;
int y = 1;

#endif

int main() {
  int z = 0;

  if (x > 0) {
    z = x;
  }

  if (y > 0) {
    z = y;
  }

  if (x > 0 || y > 0) {
    assert (z == 0);
  }
}
