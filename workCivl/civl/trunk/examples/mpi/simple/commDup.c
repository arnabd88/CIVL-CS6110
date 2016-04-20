/* commDup.c : A simple example shows how to use the MPI_Routine
   MPI_Comm_dup(MPI_Comm*).
 */
#include <mpi.h>
#include <assert.h>

int main(int argc, char * argv[]) {
  int size, rank, buf;
  MPI_Comm anotherComm;

  MPI_Init(&argc, &argv);
  MPI_Comm_rank(MPI_COMM_WORLD, &rank);
  MPI_Comm_size(MPI_COMM_WORLD, &size);
  MPI_Comm_dup(MPI_COMM_WORLD, &anotherComm);

  MPI_Reduce(&rank, &buf, 1, MPI_INT, MPI_SUM, 0, MPI_COMM_WORLD);
  MPI_Bcast(&buf, 1, MPI_INT, 0, anotherComm);
  assert(buf == ((size - 1) * size / 2));
  MPI_Comm_free(&anotherComm);
  MPI_Finalize();
  return 0;
}
