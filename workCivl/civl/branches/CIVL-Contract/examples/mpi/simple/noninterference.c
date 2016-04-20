/* Illustrates non-interference of collectives and point-to-point operations.
 * Program is erroneous since MPI_Recv cannot receive message from Bcast. */
#include <mpi.h>

double x;

void main() {
  int argc;
  char **argv;
  int rank;
  
  x = 0;
  MPI_Init(&argc,&argv);
  MPI_Comm_rank(MPI_COMM_WORLD, &rank);
  if (rank==0) {
    MPI_Bcast(&x, 1, MPI_DOUBLE, 0, MPI_COMM_WORLD);
  } else {
    MPI_Recv(&x, 1, MPI_DOUBLE, 0, MPI_ANY_TAG, MPI_COMM_WORLD, 
	     MPI_STATUS_IGNORE);
  }
  MPI_Finalize();
}
