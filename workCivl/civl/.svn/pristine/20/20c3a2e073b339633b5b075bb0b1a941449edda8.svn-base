#include <mpi.h>
#include <stdio.h>
#include <civl-mpi.cvh>

int size, rank;
int root = 0;

int main(int argc, char * argv[]) {
  int sum = 0;

  MPI_Init(&argc, &argv);
  MPI_Comm_rank(MPI_COMM_WORLD, &rank);
  MPI_Comm_size(MPI_COMM_WORLD, &size);
  for(int i = 0; i < 4; i++) {
    MPI_Reduce(&i, &sum, 1, MPI_INT, MPI_SUM, root, MPI_COMM_WORLD);
    if(!rank)printf("sum=%d\n", sum);
    $mpi_coassert(MPI_COMM_WORLD, sum@(root + 1 - 1) == (i*size));
  }
  MPI_Finalize();
  return 0;
}
