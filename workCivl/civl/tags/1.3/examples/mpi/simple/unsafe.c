#include<mpi.h>
#include<assert.h>

void main() {
  int argc;
  char **argv;
  int x, y, myrank;
	
  MPI_Init(&argc, &argv);
  MPI_Comm_rank(MPI_COMM_WORLD, &myrank);
  if (myrank==0) {
    x = 10;
    MPI_Send(&x, 1, MPI_INT, 1, 0, MPI_COMM_WORLD);
    MPI_Recv(&y, 1, MPI_INT, 1, 0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
    assert(y==20);
  } else if (myrank==1) {
    x = 20;
    MPI_Send(&x, 1, MPI_INT, 0, 0, MPI_COMM_WORLD);
    MPI_Recv(&y, 1, MPI_INT, 0, 0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
    assert(y==10);
  }
  MPI_Finalize();
}
