#include<stdlib.h>
#include<assert.h>

int f(int x){

  assert(!x);
  return x!=0;
}

int main(){
  double *p=NULL;//=malloc(sizeof(double)*10);

  f(p);
}



