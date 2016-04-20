
int f(int a, int b, int c) {
  return a+b+c;
}

int g(int n) {
  return f(n,2*n,3*n);
}

int main() {
  return g(10);
}
