/* Out of order gathers.  Error should be detected
 * with -deadlock=potential.
 */
#include<mpi.h>
#include<stdlib.h>

int nprocs;
int myrank;

void main() {
  int argc;
  char **argv;
  double x;
  double *buf;
    
  MPI_Init(&argc, &argv);
  MPI_Comm_rank(MPI_COMM_WORLD, &myrank);
  MPI_Comm_size(MPI_COMM_WORLD, &nprocs);
  x=myrank;
  buf = (double*)malloc(nprocs*sizeof(double));
  if (myrank == 0) {
    MPI_Gather(&x, 1, MPI_DOUBLE, buf, 1, MPI_DOUBLE, 0, MPI_COMM_WORLD);
    MPI_Gather(&x, 1, MPI_DOUBLE, buf, 1, MPI_DOUBLE, 1, MPI_COMM_WORLD);
  } else {
    MPI_Gather(&x, 1, MPI_DOUBLE, buf, 1, MPI_DOUBLE, 1, MPI_COMM_WORLD);
    MPI_Gather(&x, 1, MPI_DOUBLE, buf, 1, MPI_DOUBLE, 0, MPI_COMM_WORLD);
  }
  MPI_Finalize();
}
