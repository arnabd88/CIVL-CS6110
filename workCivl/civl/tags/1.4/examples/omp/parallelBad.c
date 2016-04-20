#include <civlc.cvh>

int main() {
  int counter = 0;

  #pragma omp parallel
  if (counter == 0)
    counter++;
  $assert(counter == 1);
}
