struct tm;
char* asctime(struct tm* timeptr);
struct tm{ int x; };
int main() {
  asctime((struct tm*)0);
  return 0;
}
