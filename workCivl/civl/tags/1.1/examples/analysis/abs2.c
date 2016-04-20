#include <stdlib.h>
#include <civlc.cvh>

$input int x;
$input int y;
$assume(y<0);
void main(){
  //abs(x*x*x-3*x*x+2*x-1);
  abs(y*y*y-3*y*y+2*y-1);
}
