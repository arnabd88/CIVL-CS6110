
/*@ requires a>0;
  @ ensures \result==a*2;
  @ depends \write(a), \read(a);
  @ behavior aaa:
  @   assumes a<0;
  @   ensures \result < 0;
  @ behavior bbb:
  @   assumes a==9;
  @   ensures \result==10;
  @*/
int f(int a){
  return a*2;
}
