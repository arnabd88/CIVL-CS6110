#ifdef _CIVL
#include <civlc.cvh>
#endif

int N;
#pragma CIVL $assume(N>0);
int main() {
  return N;
}
