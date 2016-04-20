#ifdef _CIVL
#include <civlc.cvh>
#endif
/* diffusion1d.c: parallel 1d-diffusion solver with constant boundary.
 * To execute: mpicc diffusion1d.c ; mpiexec -n 4 ./a.out
 * Or replace "4" with however many procs you want to use.
 * To verify: civl verify diffusion1d.c
 */
#include <stdlib.h>
#include <stdio.h>
#include <assert.h>
#include <mpi.h>
#define OWNER(index) ((nprocs*(index+1)-1)/nx)

#ifdef _CIVL

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
double oracle[nsteps][nx+2]; // solution computed sequentially, proc 0 only
int _mpi_nprocs_lo = 1;
int _mpi_nprocs_hi = 3;

#else

int nx;
double k;
int nsteps;
int wstep;

#endif

/* Global variables */

double lbound; /* left fixed boundary value */
double rbound; /* right fixed boundary value */
double *u;     /* temperature function, local */
double *u_new; /* second copy of temperature function, local */
int nprocs;    /* number of processes */
int rank;      /* the rank of this process */
int left;      /* rank of left neighbor */
int right;     /* rank of right neighbor on torus */
int nxl;       /* horizontal extent of one process */
int first;     /* global index for local index 0 */
double *buf;   /* temp. buffer used on proc 0 only */
int print_pos; /* number of cells printed on current line */
int time=0;    /* current time step */


/* Returns the global index of the first cell owned
 * by the process with given rank */
int firstForProc(int rank) {
  return (rank*nx)/nprocs;      
}

/* Returns the number of cells owned by the process
 * of the given rank (excluding ghosts) */
int countForProc(int rank) {
  int a = firstForProc(rank+1);
  int b = firstForProc(rank);

  return a-b;
}

/* Initializes the global variables.
 * Precondition: the configuration parameters have
 * already been set. */
void init_globals() { 
  MPI_Comm_size(MPI_COMM_WORLD, &nprocs);
  MPI_Comm_rank(MPI_COMM_WORLD, &rank);
  // nxl: number actual points (incl. end-points)
  // nxl+2: size of array (incl. ghost cells)
  first = firstForProc(rank);  
  nxl = countForProc(rank);
  left = first==0 || nxl==0 ? MPI_PROC_NULL : OWNER(first-1);
  right = first+nxl >= nx || nxl == 0 ? MPI_PROC_NULL : OWNER(first+nxl);
  u = (double*)malloc((nxl+2)*sizeof(double));
  assert(u);
  u_new = (double*)malloc((nxl+2)*sizeof(double));
  assert(u_new);
  if (rank == 0)
    buf = (double*)malloc((1+nx/nprocs)*sizeof(double));
}

void initialize() {
#ifdef _CIVL
  //elaborate nx to concrete value...
  //for (int i=0; i<nx; i++);
  // initialize globals and u...
  init_globals();
  lbound = U_INIT[0];
  rbound = U_INIT[nx+1];
  for (int i=1; i<=nxl; i++)
    u[i] = U_INIT[first+i];
  if (rank == 0) {
    // compute the oracle...
    for (int i=0; i<nx+2; i++)
      oracle[0][i]=U_INIT[i];
    for (int t=1; t<nsteps; t++) {
      oracle[t][0] = lbound;
      for (int i=1; i<=nx; i++)
        oracle[t][i] = oracle[t-1][i] + 
          k*(oracle[t-1][i+1] + oracle[t-1][i-1]
             - 2*oracle[t-1][i]);
      oracle[t][nx+1] = rbound;
    }
  }
#else
  nx = 10;
  k = 0.2;
  nsteps = 20;
  wstep = 2;
  lbound = rbound = 0.0;
  init_globals();
  for (int i=1; i<=nxl; i++)
    u[i]=100.0;
#endif
  if (nx>=1 && rank == OWNER(0))
    u[0] = u_new[0] = lbound;
  if (nx>=1 && rank == OWNER(nx-1))
    u[nxl+1] = u_new[nxl+1] = rbound;
  //if (rank == 0)
    //printf("nx=%d, k=%lf, nsteps=%d, wstep=%d, nprocs=%d\n",
    //     nx, k, nsteps, wstep, nprocs);
}

/* Prints header for time step.  Called by proc 0 only */
void print_time_header() {
  //printf("======= Time %d =======\n", time);
  print_pos = 0;
}

/* Prints one cell.  Called by proc 0 only. */
void print_cell(double value) {
  //printf("%7.2f\n", value);
#pragma CIVL $assert(value == oracle[time][print_pos], \
  "Error: disagreement at time %d position %d: saw %lf, expected %lf",  \
  time, print_pos, value, oracle[time][print_pos]);
  print_pos++;
}

/* Prints the current values of u. */
void write_frame() {
  if (rank != 0) {
    $elaborate(nxl);
    MPI_Send(u+1, nxl, MPI_DOUBLE, 0, 0, MPI_COMM_WORLD);
  } else {
    print_time_header();
    print_cell(lbound); // left boundary
    for (int source = 0; source < nprocs; source++) {
      int count;

      if (source != 0) {
        MPI_Status status;

        MPI_Recv(buf, 1+nx/nprocs, MPI_DOUBLE, source, 0, MPI_COMM_WORLD,
                 &status);
        MPI_Get_count(&status, MPI_DOUBLE, &count);
      } else {
        for (int i = 1; i <= nxl; i++)
          buf[i-1] = u[i];
        count = nxl;
      }
      for (int i = 0; i < count; i++)
        print_cell(buf[i]);
    }
    print_cell(rbound); // right boundary
    //printf("\n");
  }
}

/* exchange_ghost_cells: updates ghost cells using MPI communication */
void exchange_ghost_cells() {
  MPI_Sendrecv(&u[1], 1, MPI_DOUBLE, left, 0,
               &u[nxl+1], 1, MPI_DOUBLE, right, 0,
               MPI_COMM_WORLD, MPI_STATUS_IGNORE);
  MPI_Sendrecv(&u[nxl], 1, MPI_DOUBLE, right, 0,
               &u[0], 1, MPI_DOUBLE, left, 0,
               MPI_COMM_WORLD, MPI_STATUS_IGNORE);
}

/* Updates u_new using u, then swaps u and u_new.
 * Reads the ghost cells in u.  Purely local operation. */
void update() {
  for (int i = 1; i <= nxl; i++)
    u_new[i] = u[i] + k*(u[i+1] + u[i-1] - 2*u[i]);
  double * tmp = u_new; u_new=u; u=tmp;
}

/* Executes the simulation. */
int main(int argc, char *argv[]) {
  MPI_Init(&argc, &argv);
  initialize();
  write_frame();
  printf("nx = %d", nx);
  for (time=1; time < nsteps; time++) {
    exchange_ghost_cells();
    update();
    if (time%wstep==0)
      write_frame();
  }
  MPI_Finalize();
  free(u);
  free(u_new);
  if (rank == 0)
    free(buf);
  return 0;
}
