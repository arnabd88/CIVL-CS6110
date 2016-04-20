/* wildcard_coassert_bad: A root process receives messages twice from
   every other process using a wildcard receive. This program has a
   data race-condition. */
#include <mpi.h>
#include <stdio.h>
#include <civl-mpi.cvh>
#define comm MPI_COMM_WORLD
int size, rank, x;
int root = 0;

void recv(int iter) 
$requires {iter >= 0 && rank == 0}
$ensures {$collective(comm) $true} 
{
  for(int i = 1; i < size; i++)
    MPI_Recv(&x, 1, MPI_INT, MPI_ANY_SOURCE, 0, comm, MPI_STATUS_IGNORE);
  //$mpi_coassert(comm, x == iter);
}

void send(int msg) 
$ensures {$collective(comm) x@root == msg}
{
  MPI_Send(&msg, 1, MPI_INT, root, 0, comm);
  printf("Proc:%d sends %d\n", rank, msg);
  //$mpi_coassert(comm, x@root == msg);
}

int main(int argc, char * argv[]) {
  MPI_Init(&argc, &argv);
  MPI_Comm_rank(comm, &rank);
  MPI_Comm_size(comm, &size);
  for(int i = 0; i < 2; i++)
    if(!rank)
      recv(i);
    else
      send(i);
  MPI_Finalize();
  return 0;
}
