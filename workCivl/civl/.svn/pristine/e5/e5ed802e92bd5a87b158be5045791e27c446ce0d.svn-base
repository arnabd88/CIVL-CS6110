/* Out of order broadcasts.  Error should be detected
 * with -deadlock=potential.
 */
#include<mpi.h>

int nprocs;
int myrank;

void main() {
  int argc;
  char **argv;
  double x;
  double y;
    
  x=0;
  y=1;
  MPI_Init(&argc, &argv);
  MPI_Comm_rank(MPI_COMM_WORLD, &myrank);
  if (myrank == 0) {
    MPI_Bcast(&x, 1, MPI_DOUBLE, 0, MPI_COMM_WORLD);
    MPI_Bcast(&y, 1, MPI_DOUBLE, 1, MPI_COMM_WORLD);
  } else {
    MPI_Bcast(&x, 1, MPI_DOUBLE, 1, MPI_COMM_WORLD);
    MPI_Bcast(&y, 1, MPI_DOUBLE, 0, MPI_COMM_WORLD);
  }
  MPI_Finalize();
}
