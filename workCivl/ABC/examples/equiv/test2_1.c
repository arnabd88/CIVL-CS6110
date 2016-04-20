/*
 * test2_0.c and test2_1.c are not equivalent because 
 * they access different element of b at the last line.
*/

void main(){
  int a = 10;
  int b[5];

  b[0] = 1;
  b[1] = 2;
  a = a + 1;
  a = a + b[1];
}
