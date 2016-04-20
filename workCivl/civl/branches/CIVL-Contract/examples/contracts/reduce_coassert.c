/* Reduce_coassert: All processes in the MPI_COMM_WORLD sum up their
   ranks, the result is reduced to a root process. */
#include <mpi.h>
#include <stdio.h>
#include <civl-mpi.cvh>

int size, rank;
int root = 0, sum;

int main(int argc, char * argv[]) {
  MPI_Init(&argc, &argv);
  MPI_Comm_rank(MPI_COMM_WORLD, &rank);
  MPI_Comm_size(MPI_COMM_WORLD, &size);
  for(int i = 0; i < 4; i++) {
    MPI_Reduce(&i, &sum, 1, MPI_INT, MPI_SUM, root, MPI_COMM_WORLD);
    if(!rank)printf("iteration: %d  sum=%d\n", i, sum);
    $mpi_coassert(MPI_COMM_WORLD, sum@root == (i*size));
  }
  MPI_Finalize();
  return 0;
}
