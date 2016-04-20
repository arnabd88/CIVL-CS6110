/*@ 
  @ requires x >= 0;
  @ ensures \result == x + 1;
  @
*/
int add(int x) 
{
  return x + 1;
}

/*@ requires \valid(x + (0 .. 2));
  @ ensures *x == \result - 1;
  @ ensures \valid(x);
  @*/
int incr(int * x) 
{ 
  int ret = *x;
  
  ret = add(ret);
  return ret;
}

int main() {
  incr((void *)-1);
  return 0;
}
