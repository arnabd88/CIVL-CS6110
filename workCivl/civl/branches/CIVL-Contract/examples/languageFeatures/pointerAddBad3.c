#include <stdio.h>

int main(int argc, char * argv[]) {
  int a[3];
  int *p = a + 100;

  printf("%p", p);
}

