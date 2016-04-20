#include <mpi.h>
#include <stdio.h>
#include <civlc.cvh>

#define FROMRIGHT 0
#define FROMLEFT  1

$input int _mpi_nprocs = 3;
int main(int argc, char * argv[]) {
  int rank, size;
  int recv;
  int left, right;

  MPI_Init(&argc, &argv);
  MPI_Comm_rank(MPI_COMM_WORLD, &rank);
  MPI_Comm_size(MPI_COMM_WORLD, &size);
  left = (rank == 0) ? size - 1 : rank - 1;
  right = (rank == (size - 1)) ? 0 : rank + 1;
  MPI_Sendrecv(&rank, 1, MPI_INT, left, FROMRIGHT, &recv, 1, MPI_INT, 
	       right, FROMRIGHT, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
  $assert(recv == right);
  MPI_Sendrecv(&rank, 1, MPI_INT, right, FROMLEFT, &recv, 1, 
  	       MPI_INT, left, FROMLEFT, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
  $assert(recv == left);
  MPI_Finalize();
  return 0;
}
