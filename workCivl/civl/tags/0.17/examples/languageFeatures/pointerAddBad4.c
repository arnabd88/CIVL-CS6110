#include <assert.h>

int main(int argc, char * argv[]) {
  int a[2][2][2] = {{{0,1}, {2,3}}, {{4,5}, {6,7}}};
  int *p = &a[0][0][0];
  int t;

  p += 9;
}
