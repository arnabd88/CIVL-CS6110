#include <assert.h>
#include <civlc.cvh>
#include <stdlib.h>

$input int NXB = 5;           // upper bound on nx
$input int nx;               // global number of points excl. boundary
$assume(1<=nx && nx<=NXB);
$input double U_INIT[nx+2];  // initial values for temperature incl. boundary
$input double k;             // the constant D*dt/(dx*dx)
$assume(k>0 && k<.5);
$input int NSTEPS_BOUND=5;    // upper bound on nsteps
$input int nsteps;           // number of time steps
$assume(1<=nsteps && nsteps<=NSTEPS_BOUND);
$input int wstep;            // write frame every this many time steps
$assume(1<=wstep && wstep<=nsteps);
$output double output[nsteps][nx+2]; // solution computed sequentially, proc 0 only

double *u;     /* temperature function, local */
double *u_new; /* second copy of temperature function, local */

int initialize() {
  u = (double*)malloc((nx+2)*sizeof(double));
  assert(u);
  u_new = (double*)malloc((nx+2)*sizeof(double));
  assert(u_new);
  for (int i=1; i<nx+1; i++)
    u[i] = U_INIT[i];
  u[0] = u_new[0] = U_INIT[0];
  u[nx+1] = u_new[nx+1] = U_INIT[nx+1];
}

void update() {
  double * tmp;

  for(int i = 1; i <= nx; i++)
    u_new[i] = u[i] + k * (u[i+1] + u[i-1] - 2 * u[i]);
  tmp = u;
  u = u_new;
  u_new = tmp;
}

void write_frame(int time) {
  for(int i = 0; i <nx+2; i++)
    output[time][i] = u[i];
}

int main() {
  int time = 0;

  initialize();
  write_frame(time);
  for(time=1; time<nsteps; time++) {
    update();
    if (time%wstep==0)
      write_frame(time);
  }
  free(u);
  free(u_new);
  return 0;
}
