/* a_1.c.  To be linked with a_0.c and a_2.c. In this translation
 * unit, struct S is incomplete, and is therefore compatible with the
 * struct S in a_0 and the struct S in a_2, even though struct S in
 * a_0 is incompatible with that in a_2.
 */
struct S;
int f(struct S *p); // defined in a_0.c
int h(struct S *p) { // called from a_2.c
  return f(p);
}
