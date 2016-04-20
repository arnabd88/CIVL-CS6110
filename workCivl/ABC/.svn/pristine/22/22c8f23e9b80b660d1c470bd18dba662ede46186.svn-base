/* completeStruct.c: example where a structure is first declared
 * in an incomplete state, then a typdef is made to that type,
 * then the structure is completed, then the typedef is used.
 * The use should work because the typedef is like a reference to
 * the type which was completed.
 */
 
struct foo;
typedef struct foo Foo;
struct foo {int x;};
int main() {
  Foo f;
  f.x = 1;
  return f.x;
}
