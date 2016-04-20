/* Coverage test example: This example is only used for software
   testing coverage, it may not be understandable for human beings. */
#include <mpi.h>
#include <stdio.h>
#include <civl-mpi.cvh>

$input int in;
int size, rank, x;
int root = 0;

void recv(int iter) {
  for(int i = 1; i < size; i++)
    MPI_Recv(&x, 1, MPI_INT, MPI_ANY_SOURCE, 0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
  $mpi_coassert(MPI_COMM_WORLD, root == in);
  printf("rank:%d  in=%d\n", rank, in);
}

void send(int msg) {
  MPI_Send(&msg, 1, MPI_INT, root, 0, MPI_COMM_WORLD);
  printf("Proc:%d sends %d\n", rank, msg);
  $mpi_coassert(MPI_COMM_WORLD, $true);
  printf("rank:%d  in=%d\n", rank, in);
}

int main(int argc, char * argv[]) {
  MPI_Init(&argc, &argv);
  MPI_Comm_rank(MPI_COMM_WORLD, &rank);
  MPI_Comm_size(MPI_COMM_WORLD, &size);
  for(int i = 0; i < 2; i++)
    if(!rank)
      recv(i);
    else
      send(i);
  MPI_Finalize();
  return 0;
}
