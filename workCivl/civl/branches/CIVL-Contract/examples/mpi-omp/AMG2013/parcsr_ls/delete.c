#include <omp.h>

int main () 
{
  int x = 0;
  int i;
  
  #pragma omp parallel
  {
    if(x){
      i = 1;
    } else {
      i = 0;
    }
    
  }  
  
}
