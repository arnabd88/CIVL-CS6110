#include<stdio.h>

enum a {A};
enum a; // refers to same enum as above

int main() {
  enum a x=A; // refers to enum above in root scope
  printf("%d\n", x); // prints 0
  enum a {B,A}; // a new enum in this scope
  enum a y=A; // refers to new enum and new A in this scope
  printf("%d\n", y); // prints 1
  return 0;
}
