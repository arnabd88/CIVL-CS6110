#include<mpi.h>
#include<assert.h>
#include<stdio.h>
#include<civlc.cvh>

double * u;
int nx = 10;

/*@
  @ \mpi_collective(MPI_COMM_WORLD, P2P):
  @   requires \mpi_comm_size >= 2;
  @   requires \mpi_comm_rank == x;
  @*/
void exchange(int x) {
  int y;
  int left, right;
  int nprocs;
  
  MPI_Comm_size(MPI_COMM_WORLD, &nprocs);
  left = x - 1 >=0 ? x - 1 : nprocs - 1;
  right = x + 1 < nprocs ? x + 1 : 0;
  //printf("rank x=%d, send to %d, recv from %d\n", x, left, right);
  MPI_Sendrecv(&x, 1, MPI_INT, left, 0, &y, 
	       1, MPI_INT, right, 0, 
	       MPI_COMM_WORLD, MPI_STATUS_IGNORE);
  MPI_Sendrecv(&x, 1, MPI_INT, left, 0, &y, 
	       1, MPI_INT, right, 0, 
	       MPI_COMM_WORLD, MPI_STATUS_IGNORE);
}


int main() {
  int dummy = 7;
  exchange(0);
  dummy=8;
  $havoc(NULL);
  return 0;
}
