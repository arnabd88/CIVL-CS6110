void* f(int a){
  return a;
}

void* g(int t){
  return t;
}

int h(void* x){
  return x;
}

int main(){
  int t, *p=&t;

  f(p);
  g(t);
  h(t);
}
