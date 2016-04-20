/* commDupBad.c : A simple buggy example related to the MPI routine:
   MPI_Comm_dup(MPI_Comm *).
 */
#include <mpi.h>

int main(int argc, char * argv[]) {
  int size, rank;
  MPI_Comm anotherComm;
  double buf;

  MPI_Init(&argc, &argv);
  MPI_Comm_rank(MPI_COMM_WORLD, &rank);
  MPI_Comm_size(MPI_COMM_WORLD, &size);
  MPI_Comm_dup(MPI_COMM_WORLD, &anotherComm);

  buf = 2.0;
  if(rank == 0) {
    for(int i = 1 ; i < size; i++)
      MPI_Send(&buf, 1, MPI_DOUBLE, i, 0, MPI_COMM_WORLD);
  }else
    MPI_Recv(&buf, 1, MPI_DOUBLE, 0, 0, anotherComm, MPI_STATUS_IGNORE);
  MPI_Comm_free(&anotherComm);
  MPI_Finalize();
  return 0;
}
