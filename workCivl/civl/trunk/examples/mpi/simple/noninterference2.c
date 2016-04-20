/* Illustrates non-interference of collectives and point-to-point operations.
 * Program is erroneous since a collective is interspersed between a matching
 * send and recv.   It will work correctly if buffering, but not synchronously.
 */
#include <mpi.h>

double x;
double y;

void main() {
  int argc;
  char **argv;
  int rank;
  
  x = 0;
  y = 0;
  MPI_Init(&argc,&argv);
  MPI_Comm_rank(MPI_COMM_WORLD, &rank);
  if (rank==0) {
    MPI_Send(&x, 1, MPI_DOUBLE, 1, 0, MPI_COMM_WORLD);
  }
  MPI_Bcast(&y, 1, MPI_DOUBLE, 0, MPI_COMM_WORLD);
  if (rank==1) {
    MPI_Recv(&x, 1, MPI_DOUBLE, 0, MPI_ANY_TAG, MPI_COMM_WORLD,
	     MPI_STATUS_IGNORE);
  }
  MPI_Finalize();
}
