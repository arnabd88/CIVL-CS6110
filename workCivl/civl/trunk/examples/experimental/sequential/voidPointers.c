/*@ requires \valid(x + (0 .. 2));
  @ ensures \valid(x + (0 .. 2));
  @*/
int incr(void * x) 
{ 
  int * y;
  int ret;

  y = (int*)x;
  return (y[0] + 1);
}

int main() {
  incr((void *)-1);
  return 0;
}
