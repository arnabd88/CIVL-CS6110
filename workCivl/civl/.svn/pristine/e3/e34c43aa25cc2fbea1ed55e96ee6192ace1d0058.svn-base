/* wave1d.c: parallel 1d-wave equation solver with constant boundary.
 * To execute: mpicc wave1d.c ; mpiexec -n 4 ./a.out
 * Or replace "4" with however many procs you want to use.
 * To verify: civl verify wave1d.c
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <math.h>
#include <mpi.h>

#define SQR(x) ((x)*(x))
#define OWNER(index) ((nprocs*(index+1)-1)/nx)

/* MPI message tags */
#define FROMLEFT     1
#define FROMRIGHT    2
#define DATAPASS     3

/* Input parameters */
#ifdef _CIVL
#include <civlc.cvh>

$input int NXB = 5;               /* upper bound on nx */
$input int nx;                    /* number of discrete points including endpoints */
$assume(2 <= nx && nx <= NXB);     /* setting bounds */
$input double c;                  /* physical constant to do with string */
$assume(c > 0.0);       
$input int NSTEPSB = 5;        
$input int nsteps;                /* number of time steps */
$assume(0 < nsteps && nsteps <= NSTEPSB);
$input int wstep = 1;             /* number of time steps between printing */
$input int _mpi_nprocs_lo = 1;
$input int _mpi_nprocs_hi = 4;
double oracle[nsteps + 1][nx + 2];/* result of sequential run at every time step */
$input double u_init[nx];         /* arbitrary initial position of string */

#else

int nx, height_init, width_init;
int nsteps, wstep;
double c;

#endif

/* Global varibales */
double *u_prev, *u_curr, *u_next;
double k;
int nprocs, nxl, rank;
int first;                       /* global index of first cell owned by this process */
int left, right;                 /* ranks of left neighbor and right neighbor */

/* Returns the global index of the first cell owned
 * by the process with given rank */
int firstForProc(int rank) {
  return (rank*nx)/nprocs;      
}

/* Returns the number of cells the given process owns */
int countForProc(int rank) {
  int a = firstForProc(rank);
  int b = firstForProc(rank + 1);

  return b - a;
}

#ifndef _CIVL

/* Some particular initial condition for testing only */
void init(int first, int nxl) {
  int i;
  double e = exp(1.0);

  for(i = 1; i < nxl+1; i++) {
    int idx = first + i - 1;

    if(idx == 1 || idx >= width_init)
      u_prev[i] = 0.0;
    else
      u_prev[i] = height_init * e *
	exp(-1.0/(1-SQR(2.0*(idx-width_init/2.0)/width_init)));
  }
}

#endif

/* Update cells owned by processes */
void update() {
  int i;
  double *tmp;

  for (i = 1; i < nxl + 1; i++){
    u_next[i] = 2.0*u_curr[i] - u_prev[i] +
      k*(u_curr[i+1] + u_curr[i-1] -2.0*u_curr[i]);
  }
  //cycle pointers:
  tmp = u_prev;
  u_prev = u_curr;
  u_curr = u_next;
  u_next = tmp;
}

/* Initialization function, initializes all parameters and data array.
 * In CIVL mode, process 0 runs the complete problem sequentially to
 * create the oracle which will be compared with the results of the
 * parallel run.
 */
void initialization() {
  int i, j;

#ifndef _CIVL

  nx = 50;
  c = 0.3;
  height_init = 10;
  width_init = 10;
  nsteps = 500;
  wstep = 5;

#endif

  assert(nx >= 2);
  assert(c > 0);
  assert(nsteps >= 1);
  assert(wstep >= 1 && wstep <= nsteps);
  k = c * c;
  printf("Wave1d with nx=%d, c=%f, nsteps=%d, wstep=%d\n", nx, c, nsteps, wstep);

#ifdef _CIVL

  // If in CIVL verification mode and rank is 0,
  // do a sequential run and store result in "oracle" 
  // for comparison later
  if(rank == 0) { 
    // sets constant boundaries for first string and
    // it's virtual previous string
    oracle[0][0] = 0;
    oracle[0][nx + 1] = 0;
    // initialization for first string and
    // it's virtual previous string
    for(i = 1; i < nx + 1; i++) {
      oracle[0][i] = u_init[i - 1];
      oracle[1][i] = u_init[i - 1];
    }
    for(i = 1; i < nsteps; i++){
      oracle[i][0] = 0;
      oracle[i][nx + 1] = 0; 
      // update
      for (j = 1; j < nx + 1; j++)
	oracle[i+1][j] = 2.0*oracle[i][j] - oracle[i-1][j] +
	  k*(oracle[i][j+1] + oracle[i][j-1] -2.0*oracle[i][j]);
    }
  }

#endif

  nxl = countForProc(rank);
  first = firstForProc(rank);
  u_prev = (double *)malloc((nxl + 2) * sizeof(double));
  assert(u_prev);
  u_curr = (double *)malloc((nxl + 2) * sizeof(double));
  assert(u_curr);
  u_next = (double *)malloc((nxl + 2) * sizeof(double));
  assert(u_next);
  // sets constant boundaries
  u_prev[0] = 0;
  u_curr[0] = 0;
  u_next[0] = 0;
  u_prev[nxl + 1] = 0;
  u_curr[nxl + 1] = 0;
  u_next[nxl + 1] = 0;
  // skip processes which are allocated no cells
  if(first != 0 && nxl != 0)
    left = OWNER(first - 1);
  else 
    left = MPI_PROC_NULL;
  if(first + nxl < nx && nxl != 0)
    right = OWNER(first + nxl);
  else
    right = MPI_PROC_NULL;
}

/* Print out the value of data cells; 
   Do comparison in CIVL mode */
void printData (int time, int first, int length, double * buf) {
  int i;

  for(i = 0; i < length; i++){
    printf("u_curr[%d]=%8.8f   ", first + i, buf[i]);
#ifdef _CIVL

     $assert((oracle[time + 1][first + i + 1] == buf[i]), \
    "Error: disagreement at time %d position %d: saw %lf, expected %lf", \
    time, first + i, buf[i], oracle[time + 1][first + i + 1]);

#endif
    printf("\n");
  }
}

/* receives data from other processes and wirte frames */
void write_frame (int time) {
  if(rank == 0) {
    double  buf[nx + 2];
    MPI_Status status;

    printf("\n======= Time %d =======\n", time);
    printData(time, first, nxl, &u_curr[1]);
    for(int i=1; i < nprocs; i++) {
      int displ = firstForProc(i);
      int count;

      MPI_Recv(buf, nx, MPI_DOUBLE, i, DATAPASS, MPI_COMM_WORLD, &status);
      MPI_Get_count(&status, MPI_DOUBLE, &count);
      printData(time, displ, count, buf);
    }
    printf("\n");
  } else 
    MPI_Send(&u_curr[1], nxl, MPI_DOUBLE, 0, DATAPASS, MPI_COMM_WORLD);
}

/* Exchanging ghost cells */
void exchange(){
  MPI_Sendrecv(&u_curr[1], 1, MPI_DOUBLE, left, FROMRIGHT, &u_curr[nxl+1], 1, MPI_DOUBLE, 
	       right, FROMRIGHT, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
  MPI_Sendrecv(&u_curr[nxl], 1, MPI_DOUBLE, right, FROMLEFT, &u_curr[0], 1, 
	       MPI_DOUBLE, left, FROMLEFT, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
}

int main(int argc, char * argv[]) {
  int iter;


  //#ifdef _CIVL

  // elaborate nx to concrete value...
  //$elaborate(nx);

  //#endif
  MPI_Init(&argc, &argv);
  MPI_Comm_rank(MPI_COMM_WORLD, &rank);
  MPI_Comm_size(MPI_COMM_WORLD, &nprocs); 
  initialization();
#ifdef _CIVL

  if(nxl != 0) {
    memcpy(&u_curr[1], &u_init[first], sizeof(double) * nxl);
    memcpy(&u_prev[1], &u_curr[1], sizeof(double) * nxl);
  }

#else

  if(nxl != 0) {
    init(first, nxl);
    memcpy(&u_curr[1], &u_prev[1], nxl * sizeof(double));
  }

#endif
  for(iter = 0; iter < nsteps; iter++) {
    if(iter % wstep == 0)
	write_frame(iter);
    if(nxl != 0){
      exchange();
      update();
    }
  }
  free(u_curr);
  free(u_prev);
  free(u_next);
  MPI_Finalize(); 
  return 0;
}
