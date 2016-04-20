/*
 * Expected result are:
 *   main calls {main, foo, bar} <- due to imprecision
 *   foo called by {main}
 *   bar called by {main}
 */

int foo() {
  return 0;
}

int bar() {
  return 1;
}

// not included as a callee of main due to parameter
int bat(int x) {
  return x;
}

// not included as a callee of main due return type
double bas() {
  return 0.0;
}


int main() {
  int (*fun)(void) = foo;
  int x = (fun)(); 
}
