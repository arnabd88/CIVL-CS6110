#include<mpi.h>
#include<assert.h>

int nprocs;
int myrank;


void main() {
  int argc;
  char **argv;
  double buf[3];
  MPI_Status status;
  int count;

  MPI_Init(&argc, &argv);
  MPI_Comm_rank(MPI_COMM_WORLD, &myrank);
  if(myrank == 0) {
    buf[0] = 1.0;
    buf[1] = 1.1;
    MPI_Send(&buf[0], 2, MPI_DOUBLE, 1, 0, MPI_COMM_WORLD);
  } else {
    buf[0] = 0.0;
    buf[1] = 0.0;
    buf[2] = 0.0;
    MPI_Recv(&buf[0], 3, MPI_DOUBLE, 0, 0, MPI_COMM_WORLD, &status);
    MPI_Get_count(&status, MPI_DOUBLE, &count);
    assert(count == 2);
    assert(buf[0] == 1.0 && buf[1] == 1.1 && buf[2] == 0.0);
  }
  MPI_Finalize();
}
