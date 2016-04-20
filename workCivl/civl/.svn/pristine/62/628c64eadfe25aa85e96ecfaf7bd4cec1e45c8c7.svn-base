#include<assert.h>
#include<mpi.h>
#include<civl-mpi.cvh>
#include<stdio.h>

$input int in;
$input int _mpi_nprocs = 2;
$assume(in > 0);
MPI_Comm comm = MPI_COMM_WORLD;
int rank;

int gimmeOne(int x) 
$requires {$collective(comm) $mpi_isRecvBufEmpty(1-rank)}
$requires {$collective(MPI_COMM_WORLD) $true}
$requires {x > 0}
$ensures {$collective(MPI_COMM_WORLD) $mpi_isRecvBufEmpty(1-rank)}
$ensures {$collective(MPI_COMM_WORLD) $result == 1 + x}
$ensures {x == in}
{
  return 1 + x;
}

int main(int argc, char * argv[]) {
  int x;

  MPI_Init(&argc, &argv);
  MPI_Comm_rank(comm, &rank);
  if(rank == 1)
    MPI_Send(&rank, 1, MPI_INT, 0, 0, comm);
  x = gimmeOne(in);
  if(rank == 0)
    MPI_Recv(&x, 1, MPI_INT, 1, 0, comm, MPI_STATUS_IGNORE);
  MPI_Finalize();
}
