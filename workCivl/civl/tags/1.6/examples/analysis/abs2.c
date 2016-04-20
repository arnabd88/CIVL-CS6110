#include <stdlib.h>
#include <civlc.cvh>

$input int k;
$input int m;
$input int x;
$input int y;
$input int z;
$assume(x<0);
$assume(y>0);
$assume(k!=0);

int call1(int v){
    return abs(v);
}

int call2(int v){
    return abs(v);
}

int call3(int v){
    return abs(v);
}

int call4(int v){
    return abs(v);
}

int call5(int v){
    return abs(v);
}

int call6(int v){
    return abs(v);
}

int call7(int v){
    return abs(v);
}

void main(){
    call1(k);
    call1(z*z*z-3*z*z+2*z-1);
    call1(y);
    call1(1);
    call1(-1);
    call2(k);
    call2(m);
    call2(y);
    call3(z*z*z-3*z*z+2*z-1);
    call3(m);
    call4(m);
    call5(x);
    call5(y);
    call6(y);
    call6(x);
    call7(m);
    call7(x);
}
