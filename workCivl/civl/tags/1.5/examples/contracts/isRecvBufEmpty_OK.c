#include<assert.h>
#include<mpi.h>
#include<civl-mpi.cvh>
#include<stdio.h>

#define comm MPI_COMM_WORLD
int rank, nprocs, left, right;

int sendrecv() 
$ensures  {$collective(comm) ($mpi_isRecvBufEmpty(left) && left == $result)}
{
  int message = rank;
  int recvBuf;

  MPI_Sendrecv(&message, 1, MPI_INT, right, 0, &recvBuf, 1, MPI_INT, left, 0, comm, MPI_STATUS_IGNORE);
  return recvBuf;
}

int main(int argc, char * argv[]) {
  int x;

  MPI_Init(&argc, &argv);
  MPI_Comm_size(comm, &nprocs);
  MPI_Comm_rank(comm, &rank);
  left = (rank-1) % nprocs;
  right = (rank+1) % nprocs;
  x = sendrecv();
  MPI_Finalize();
  return 0;
}
