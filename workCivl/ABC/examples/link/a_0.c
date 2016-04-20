/* a_0.c.  To be linked with a_1.c and a_2.c.  In this translation
 * unit, struct S is complete.
 * 
 * By the end of the linking process, the functions will have the
 * following types:
 *
 * f: pointer to struct S {int x;}    -> int
 * h: pointer to struct S {double y;} -> void
 *
 * However, h may not have this type until after its body is analyzed.
 * So after analysis, if a function's type has changed, need to go
 * back and re-analyze.  If you did that you would get an error when
 * re-analyzing the body of h at the "f(p)", because the type of p
 * would be incompatible with the type expected by f.
 */
struct S {int x;};
int f(struct S *p) {
  return p->x + 1;
}
