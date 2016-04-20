#include<mpi.h>

int myrank;

void main() {  
	MPI_Comm_rank(MPI_COMM_WORLD, &myrank);
}
