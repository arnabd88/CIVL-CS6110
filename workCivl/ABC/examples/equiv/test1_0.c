/*
 * test1_0.c and test1_1.c become equivalent after pruner is applied.
*/

#include<stdio.h>

int main(){
  int a = 9;

  for(int i = 0; i < 100; i ++){
    printf("Current i is %d.\n", i);
  }
}

