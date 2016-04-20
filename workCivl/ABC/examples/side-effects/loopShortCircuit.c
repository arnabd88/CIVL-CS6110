int main(){
  int i=0;
  int j=1;

  while((i>-1) && (i++ < 10))
    j=i;
  for(;((i>-1) && (i++ < 10));j++){
    j=i+j;
  }
  do{
    j=i;
  }while((i>-1 && j--) && (i-- || i++ < 10));
}
