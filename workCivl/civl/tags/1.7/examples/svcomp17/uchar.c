#include<stdio.h>

int main(){
  unsigned char a=4, b=7;
  //int a=4, b=7;

  int d, *p=&d;
  int t=(int)(*(p+a));
  
  /*if(a & b)
    printf("true branch\n");
  else
  printf("false branch\n");*/
  t++;
}
