#include <stdio.h>
#include <stdbool.h>
#include <civlc.cvh>

/*
NOTE: THIS PROBLEM HAS NOT BEEN SOLVED YET

problem description:
Verify a function isRelaxedPrefix determining if a list _pat_ (for
pattern) is a relaxed prefix of another list _a_.

The relaxed prefix property holds iff _pat_ is a prefix of _a_ after
removing at most one element from _pat_.

examples:

pat = {1,3}   is a relaxed prefix of a = {1,3,2,3} (standard prefix)

pat = {1,2,3} is a relaxed prefix of a = {1,3,2,3} (remove 2 from pat)

pat = {1,2,4} is not a relaxed prefix of a = {1,3,2,3}.

command: civl verify RelaxedPrefix_2015_1.c

*/
$input int N1_BOUND = 4;
$input int N2_BOUND = 3;
$input int n1;
$assume (n1>=0 && n1 < N1_BOUND);
$input int X1[n1];

$input int n2;
$assume (n2>=0 && n2 < N2_BOUND);
$input int X2[n2];

bool isRelaxedPrefix(int* pat, int patLen, int* a, int aLen){
  int shift = 0;
  int i;

  if(patLen > aLen+1) return false;
  for(i=0; i<patLen; i++){
    if(i == aLen)
      return true;
    if(pat[i] != a[i-shift]){
      if(shift == 0)
        shift = 1;
      else
        return false;
    }
  }
  return true;
}

void test2(){
  bool result = isRelaxedPrefix(X1, n1, X2, n2);
  if(n1 > n2+1){
    $assert(!result);
  }else if(n1 == n2+1){
    $assert(result ==
      ($exists {int k | k >= 0 && k <n1}
        (
          ($forall {int i | i >= 0 && i < k} X1[i] == X2[i]) &&
          ($forall {int i | i > k && i < n1} X1[i] == X2[i-1])
          //$forall {int i, j | i >= 0 && i < k && j >k && j <n1} X1[i] == X2[i] && X1[j] == X2[j-1])
        )
      )
    );
  }else{
    $assert(result ==
      ($exists {int k | k >= 0 && k <=n1}
        (
          ($forall {int i | i >= 0 && i < k} X1[i] == X2[i]) &&
          ($forall {int i | i > k && i < n1} X1[i] == X2[i-1])
          //$forall {int i, j | i >= 0 && i < k && j >k && j <n1} X1[i] == X2[i] && X1[j] == X2[j-1])
        )
      )
    );
  }
}

void main(){
  test2();
}
