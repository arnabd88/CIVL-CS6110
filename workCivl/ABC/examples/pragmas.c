#include <stdio.h>

#pragma P1 this is a pragma

int n;

int main(int argc, char* argv[]) {
  printf("Hello");
#pragma P2 another pragma
  return 0;
}
