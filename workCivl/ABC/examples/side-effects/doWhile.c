int f(int i){
  return i>0;
}

int main(){
  int sum=0, i=10;

  do{
    sum += i--;
  }while(f(i));

  i=10;
  sum=0;
  do{
    sum += i;
    }while(--i);

  i=10;
  sum=0;
  do{
    sum += i;
  }while(i--);
}
