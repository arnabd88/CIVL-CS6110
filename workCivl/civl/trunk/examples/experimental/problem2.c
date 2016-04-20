/* Commandline execution:
 *		civl verify quantifiers.cvl
 * */
#include<civlc.cvh>

void main() {
  int a[5];
  for (int i = 0; i < 5; i++) {
    a[i] = i;
  }
  $assert($exists {int k | k >= 0 && k < 5} (
          ($forall {int i | i >=0 && i<=k} a[i] == i) &&
          ($forall {int i | i >k && i<5} a[i] == i)
    )
  );
}
