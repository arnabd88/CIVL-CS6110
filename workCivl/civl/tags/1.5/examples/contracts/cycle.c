/* cycle: Each process send its rank to its right neighbor and
   receives message from the left neighbor.
 */
#include<mpi.h>
#include<civl-mpi.cvh>

int main(int argc, char * argv[]) {
  int x, rank, nprocs;
  int left, right;
  MPI_Comm comm = MPI_COMM_WORLD;

  MPI_Init(&argc, &argv);
  MPI_Comm_rank(comm, &rank);
  MPI_Comm_size(comm, &nprocs);
  left = (rank + 1)%nprocs;
  right = (rank - 1)%nprocs;
  for(int i = 0; i < nprocs; i++) {
    MPI_Sendrecv(&rank, 1, MPI_INT, right, 0, 
		 &x, 1, MPI_INT, left, 0, comm,
		 MPI_STATUS_IGNORE);
    $mpi_coassert(comm, rank == x@right);
  }
  MPI_Finalize();
  return 0;
}
