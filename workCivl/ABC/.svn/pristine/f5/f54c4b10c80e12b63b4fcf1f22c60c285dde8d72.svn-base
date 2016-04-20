#include<stdio.h>
#include<stdlib.h>

struct complex_t{
  int a;
  int b;
  int c[2];
};

int main(){
  //int a[100/sizeof(int)];
  int a[1024 / (8 * (int) sizeof (int))];
  struct complex_t d={1,2,{3,4}};

  a[0]=0;
  a[1]=d.c[0];
}
