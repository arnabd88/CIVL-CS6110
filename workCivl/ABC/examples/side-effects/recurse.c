
int f(int n) {
  return f(f(f(n-3)));
}

int main() {
  return f(10);
}
