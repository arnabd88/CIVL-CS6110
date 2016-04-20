#include <omp.h>
//#include <civlc.cvh>

#define THREAD_MAX 4

int main () 
{
  int x;
  #pragma omp parallel shared(x)
  {
	x = 0;
  }
}
