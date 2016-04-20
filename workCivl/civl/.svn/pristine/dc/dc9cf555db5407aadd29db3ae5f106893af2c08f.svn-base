#include <civlc.cvh>

int dummy() {
  return 1;
}

int incr(int *x) 
  $requires {*x == 0}
{ 
  int ret = dummy();
  return ret;
}

int main() {
  /* This is a dummy main function, this main function will be
     ignored, when CIVL is in the Contract System Mode. Functions have
     to be called in order to not be pruned. */
  incr((void *)-1);
  return 0;
}
