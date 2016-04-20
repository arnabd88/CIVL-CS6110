/*
 * Expected results:
 *   main calls {foo,bar}
 *   foo calls {bar}
 *   bar calls {}
 *   main called by {}
 *   foo called by {main}
 *   bar called by {main,foo} 
 */
void bar() {
}

void foo() {
  bar();
}

int main() {
  foo();
  bar();
}
