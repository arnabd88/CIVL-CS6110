#include <mpi.h>
#include <stdio.h>
#include <civl-mpi.cvh>

int size, rank;
int root = 0;

void recv() {
  int x;

  for(int i = 1; i < size; i++)
    MPI_Recv(&x, 1, MPI_INT, MPI_ANY_SOURCE, 0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
  MPI_Barrier(MPI_COMM_WORLD);
  CMPI_Coassert(MPI_COMM_WORLD, $true);
}

void send(int msg) {
  int x;

  MPI_Send(&msg, 1, MPI_INT, root, 0, MPI_COMM_WORLD);
  printf("Process %d sends %d to root.\n", rank, msg);
  MPI_Barrier(MPI_COMM_WORLD);
  CMPI_Coassert(MPI_COMM_WORLD, root@x == msg);
}

int main(int argc, char * argv[]) {
  MPI_Init(&argc, &argv);
  MPI_Comm_rank(MPI_COMM_WORLD, &rank);
  MPI_Comm_size(MPI_COMM_WORLD, &size);
  for(int i = 0; i < 2; i++)
    if(!rank)
      recv();
    else
      send(i);
  MPI_Finalize();
  return 0;
}
