
typedef struct Value_t{
  int x;
} Value;

int main(){
  int a,*p=&a;
  Value *v;
  
  v=(Value*)p;
  v->x=5;
}
