/* a2.c. To be linked with a0.c and a1.c.  In this translation unit,
 * struct S is complete, but is not compatible with the complete
 * struct S in a0.c.  It is however compatible with the incomplete
 * struct S in a1.c.
 */
struct S {double y;};
int h(struct S *p); // defined in a_1.c
int main() {
  struct S s = {.y=3.14};
  return h(&s);
}
