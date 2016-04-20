struct emptyT{
};

void f(struct emptyT x);

int main(){
  struct emptyT s, *p;

  p=&s;
  f(s);
}
