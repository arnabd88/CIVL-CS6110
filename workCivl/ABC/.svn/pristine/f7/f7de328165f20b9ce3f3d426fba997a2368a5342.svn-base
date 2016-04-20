/* wildcard_coassert_bad: A root process receives messages twice from
   every other process using a wildcard receive. This program has a
   data race-condition. */
#include <mpi.h>
int size, rank, x;
int root = 0;
MPI_Comm comm = MPI_COMM_WORLD;

/*@
  @ requires iter >= 0 && rank == 0;
  @ \mpi_collective(comm, P2P):
  @   ensures \true;  
  @
*/
void recv(int iter) 
{
  for(int i = 1; i < size; i++)
    MPI_Recv(&x, 1, MPI_INT, MPI_ANY_SOURCE, 0, comm, MPI_STATUS_IGNORE);
}

/*@ \mpi_collective(comm, P2P):
  @   ensures x#root == msg;
  @
*/
void send(int msg) 
{
  MPI_Send(&msg, 1, MPI_INT, root, 0, comm);
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
