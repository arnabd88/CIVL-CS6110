#include<assert.h>
#include<mpi.h>
#include<civl-mpi.cvh>
#include<stdio.h>

$input int in;
$input int _mpi_nprocs = 2;
$assume(in > 0);
MPI_Comm comm = MPI_COMM_WORLD;
int rank;

/* starts from a simple clause, 
   consequent \mpi_collective blocks, not nested: */
/*@   requires x == 0;
  @ \mpi_collective(comm, BOTH):
  @   requires x == 0;
  @   ensures  x == 1;
  @ \mpi_collective(comm, BOTH):
  @   ensures  x == 1;
  @*/
int gimmeOne(int x) 
{
  return 1 + x;
}

/* starts from a \mpi_collective block: */
/*@
  @ \mpi_collective(comm, BOTH):
  @   requires x == 0;
  @   ensures  x == 1;
  @ \mpi_collective(comm, BOTH):
  @   ensures  x == 1;
  @*/
int gimmeTwo(int x) 
{
  return 2 + x;
}

/* behaviors in a \mpi_collective block: */
/*@
  @ \mpi_collective(comm, BOTH):
  @   requires x == 0;
  @   ensures  x == 1;
  @   behavior x_gt_0:
  @     assumes x >= 0;
  @     requires x != 4;
  @     ensures  x != 5;
  @ \mpi_collective(comm, BOTH):
  @   ensures  x == 1;
  @*/
int gimmeThree(int x) 
{
  return 3 + x;
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
