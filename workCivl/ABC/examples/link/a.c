// ================ a_0.c ================
struct S$TU0 {
  int x;
};
int f(struct S$TU0* p)
{
  return p->x + 1;
}
// ================ a_1.c ================
struct S;
int f(struct S* p);
int h(struct S* p) {
  return f(p);
}
// ================ a_2.c ================
struct S$TU2 {
  double y;
};
int h(struct S$TU2* p);
int main() {
  struct S$TU2 s = {.y=3.14};
  return h(&s);
}
