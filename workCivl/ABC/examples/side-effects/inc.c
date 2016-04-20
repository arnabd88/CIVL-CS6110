
int f(int n) {
  return n;
}

int main() {
  int i=10;
  int j=f(i++);
  int k=f(++i);
}
