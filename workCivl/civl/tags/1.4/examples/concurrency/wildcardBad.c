#include <stdio.h>
#include <mpi.h>

$input int _mpi_nprocs = 3;

void main(int argc, char * argv[]){
  int nprocs, rank, msg;
  MPI_Status status;

  MPI_Init(&argc, &argv);
  MPI_Comm_rank(MPI_COMM_WORLD, &rank);
  MPI_Comm_size(MPI_COMM_WORLD, &nprocs);
  if(rank != 0){
    msg = rank;
    MPI_Send(&msg, 1, MPI_INT, 0, 1, MPI_COMM_WORLD);
  }
  else{
    int source;

    msg = -1;	
    printf("I'm process %d :\n", rank);
    MPI_Recv(&msg, 1, MPI_INT, MPI_ANY_SOURCE, 1, MPI_COMM_WORLD, &status);
    MPI_Recv(&msg, 1, MPI_INT, 1, 1, MPI_COMM_WORLD, &status);
  }
  MPI_Finalize();
}
