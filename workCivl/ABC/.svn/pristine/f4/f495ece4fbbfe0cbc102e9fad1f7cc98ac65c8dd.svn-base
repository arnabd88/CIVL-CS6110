/*
 * Expected results:
 *   main calls {foo,bar}
 *   foo calls {bar}
 *   bar calls {foo}
 *   main called by {}
 *   foo called by {main, bar}
 *   bar called by {main,foo} 
 */
int x;

void foo(void);

void bar() {
  if (!x) foo();
}

void foo() {
  if (x) bar();
}

int main() {
  foo();
  bar();
}
