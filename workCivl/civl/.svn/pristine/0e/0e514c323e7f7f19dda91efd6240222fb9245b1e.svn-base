/**
 * In this example, an LHS expression contains a conditional sub-expression.
 * Previously there is a bug handling such features. 
 * Now the bug is fixed and this example is added to the regress test suite
 * for future maintenance.
 */

#include<civlc.cvh>
int main() {
  int A[10];
  int x = 6;

  A[x == 0 ? 1 : x] = 0;
  $assert(A[6]==0);
  return 0;
}
