/*
 * test4_0.c and test4_1.c are not equivalent because 
 * they have different name for the local variable of function f.
*/

int f(int k);

void main(){
  int a = 10;

  a = f(a);
}

int f(int k){
  int a0 = 9;

  return k + a0;
}
