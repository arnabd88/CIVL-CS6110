
#include<stdio.h>

struct s {int f;};

int main() {
  enum s {A,B,C};
  {
    struct s x; // error: conflicts with enum s above
    x.f=9;
    printf("%d\n", x.f);
  }
  return 0;
}
