#include<assert.h>
#include<stdio.h>
/*@
  @ ensures \result == x + y;
*/
int add(int x, int y){
  return x + y;
}

/*@ requires n >= 8 && n <= 10;
  @ ensures ((n + 1) * n) / 2 == \result;
 */
int sum1(int n) {
  int ret = 0;

  for(int i = 0; i <= n; i++) {
    printf("%d\n",i);
    ret = add(ret, i);
  }
  return ret;
}

/*@ requires n >= 0;
  @ ensures ((n + 1) * n) / 2 == \result;
 */
int sum2(int n) {
  int ret = 0;
  int arg;

  if(n <= 0) return 0;
  else{
    arg = sum2(n - 1);
    ret = add(n, arg);
  }
  return ret;
}

int main() {
  add(0,0);
  sum1(0);
  sum2(0);
}
