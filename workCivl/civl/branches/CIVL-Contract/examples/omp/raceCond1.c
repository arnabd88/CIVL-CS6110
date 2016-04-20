// a progrm with race condition
// online source: http://sourceforge.net/apps/trac/cppcheck/ticket/663

#include <omp.h>
int main()
{
	int a[50],i;
    
	a[0] = 1;
#pragma omp parallel for
	for(i=1; i<50; i++)
	{
		a[i] = i + a[i-1];
	}
}
