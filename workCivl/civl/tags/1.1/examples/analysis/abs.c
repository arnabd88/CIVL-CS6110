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
    
    a=abs(0); // 0
    a=abs(x); // -
    a=abs(y); // +
    a=abs(z); // *
    a=abs(k);
    a=abs(x*y*z); // *
    a=abs(x*y*k);
    a=abs(x*y); // -
    $assert(x*y<=0);
    
    a=abs(x%y); //+
    $assert(x%y>=0);
    
    a=abs((-x)%y); // +
    $assert((-x)%y>=0);
    
    a=abs(z%2-1);
    $assert((z%2-1)<=0);
    a=abs(z%2-2);
    $assert((z%2-2)<0);
}
