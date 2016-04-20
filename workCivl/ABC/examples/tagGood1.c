// three different entities, all with same tag but in different scopes,
// so OK
#include<stdio.h>

struct s {int f;};

int main() {
  enum s {A,B,C};
  {
    struct s {int g;} x;
    x.g=9;
    printf("%d\n", x.g);
  }
  return 0;
}
