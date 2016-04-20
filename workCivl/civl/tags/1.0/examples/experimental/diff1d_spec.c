#ifdef _CIVL
#include <civlc.cvh>
#endif
#include <stdlib.h>
#include <stdio.h>
#include <assert.h>
#include <string.h>

$input int NXB = 5;                  // upper bound on nx
$input int nx;                       // global number of points excl. boundary
$assume(1<=nx && nx<=NXB);
$input double U_INIT[nx+2];          // initial values for temperature incl. boundary
$input double k;                     // the constant D*dt/(dx*dx)
$assume(k>0 && k<.5);
$input int NSTEPS_BOUND=5;           // upper bound on nsteps
$input int nsteps;                   // number of time steps
$assume(1<=nsteps && nsteps<=NSTEPS_BOUND);
$input int wstep = 1;                // write frame every this many time steps
//$assume(1<=wstep && wstep<=nsteps);
//$assume(nsteps%wstep == 0 && wstep != 0);
$output double output[nsteps][nx+2]; // solution computed sequentially, proc 0 only

/* Global variables */
double lbound; /* left fixed boundary value */
double rbound; /* right fixed boundary value */

int main() {
  //elaborate nx to concrete value...
  elaborate(nx);
  elaborate(nsteps);
  double u[nsteps][nx+2];
  int counter = 0;

  lbound = U_INIT[0];
  rbound = U_INIT[nx+1];
  for (int i=0; i<nx+2; i++)
    u[0][i]=U_INIT[i];
  memcpy(&output[0][0], &u[0][0], (nx + 2)*sizeof(double));
  for (int t=1; t<nsteps; t++) {
    u[t][0] = lbound;
    for (int i=1; i<=nx; i++)
      u[t][i] = u[t-1][i] + 
	k*(u[t-1][i+1] + u[t-1][i-1]
	   - 2*u[t-1][i]);
    u[t][nx+1] = rbound;
    if(t%wstep == 0) {
      memcpy(&output[counter][0], &u[t][0], (nx + 2)*sizeof(double));
      counter++;
    }
  }
}

