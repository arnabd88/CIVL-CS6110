#define MAX(a,b) (((a)>=(b))?(a):(b))

void main(){
    int a=0;
    
    a = MAX(a, 1);
    a = a < 5 ? 10 : 100;
    if(a>0){
        a=1;
    }else{
        a=2;
    }
}
