#include <stdio.h>
#include <civlc.cvh>

$input int n1;
$assume (n1>=0);
$input int X1[n1];
$input int X2[n1];

void main(){
  $assert(
	  ($forall {int i | i > 0 && i < n1} X1[i] == X2[i])
	  && ($forall {int i | i > 0 && i < n1} X1[i] == X2[i])
	  );
}
