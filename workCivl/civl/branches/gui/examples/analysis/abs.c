#include <stdlib.h>
#include <civlc.cvh>

$input int k;
$input int x;
$input int y;
$input int z;
$assume(x<0);
$assume(y>0);
$assume(k!=0);
void main(){
    int a = 9;
    
    a=abs(0);
    a=abs(x); // x<0
    a=abs(y); // y>0
    a=abs(z);
    a=abs(k); // k!=0
    a=abs(x*y*z);
    a=abs(x*y*k);
    a=abs(x*y);
    $assert(x*y<=0);
    
    a=abs(y%2-1);
    a=abs(y%2-2);
}
