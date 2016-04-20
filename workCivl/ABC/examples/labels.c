void f(int a){
  int k;
  if(a == 0)
    goto ERROR;
  else
    k = a + 1;
  if(k > 100){
    ERROR:
      goto ERROR;
  }
}

int main(){
  int t = 0;
  
  if(t < 10)
    goto ERROR;
  f(t);
  if(t == 9){
    ERROR:
      goto ERROR;
  }
}
