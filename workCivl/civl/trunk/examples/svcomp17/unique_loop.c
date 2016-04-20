extern void __VERIFIER_assume(int);
extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int(void);

int main() {
  int y = 1;

  for(int i=0; i<2; i++) {
    if (y > 0) {
      y = __VERIFIER_nondet_int(); 
    }
  }

  if (y < 0) {
    ERROR: __VERIFIER_error();
  }
}
