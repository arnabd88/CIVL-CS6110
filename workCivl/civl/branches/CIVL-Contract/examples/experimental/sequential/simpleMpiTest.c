#include<mpi.h>
#include<assert.h>
#include<civlc.cvh>

double * u;
int nx = 10;

/*@
  @ \mpi_collective(MPI_COMM_WORLD, P2P):
  @   requires \mpi_comm_size == 2;
  @   requires \mpi_comm_rank == x;
  @*/
void exchange(int x) {
  int y;
  int neighbor = 1 - x;

  MPI_Sendrecv(&x, 1, MPI_INT, neighbor, 0, &y, 
	       1, MPI_INT, neighbor, 0, 
	       MPI_COMM_WORLD, MPI_STATUS_IGNORE);
  assert(x + y == 1);
}


int main() {
  int dummy = 7;
  exchange(0);
  dummy=8;
  $havoc(NULL);
  return 0;
}
