#include<mpi.h>
#include<civlc.cvh>

/*@ 
  @ requires \valid(buf + (0 .. count));
  @ \mpi_collective(comm, P2P):
  @   requires 0 <= root && root < \mpi_comm_size;
  @   requires \mpi_agree(root) && \mpi_agree(count);
  @   requires 0 < count && count < 10;
  @   ensures \mpi_equals(buf, count, MPI_INT, \remote(buf, root));
  @*/
int broadcast(int * buf, int count, 
	      MPI_Datatype datatype, int root, MPI_Comm comm) {
  int nprocs, rank;
  int tag = 999;

  MPI_Comm_size(comm, &nprocs);
  MPI_Comm_rank(comm, &rank);
  if (rank == root) {
    for (int i = 0; i < nprocs; i++)
      if (i != root)
	MPI_Send(buf, count, MPI_INT, i, tag, comm);
  } else
    MPI_Recv(buf, count, MPI_INT, root, tag, comm,
	     MPI_STATUS_IGNORE);
  return 0;
}


int main() {
  broadcast(NULL, 0, MPI_INT, 0, (MPI_Comm)0);
  return 0;
}
