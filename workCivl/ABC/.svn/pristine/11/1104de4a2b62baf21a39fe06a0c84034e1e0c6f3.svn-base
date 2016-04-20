/* Should give syntax error */
#include<stdio.h>



double a[3][4];

void f(double **p) {
  printf("%f\n", p[2][3]);
  fflush(stdout);
}

int main() {
  a[2][3] = 3.1415;
  f(a);
  return 0;
}
