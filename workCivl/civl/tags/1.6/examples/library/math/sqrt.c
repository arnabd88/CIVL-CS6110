#include<assert.h>
#include<math.h>
#include<stdio.h>

int main(int argc, char** argv) {
  double a = 1.0/4.0;
  double b = 1.0/3.0;
  double c = 1.0;
  double x = (sqrt(c)*sqrt(c)*b - a)/(sqrt(c)*sqrt(c));
  printf("FOO: %f\n", x);
  x = sqrt(x);
  printf("BAR: %f\n", x);
}

