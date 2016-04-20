#include<mpi.h>

int myrank;

void main() {
	int argc;
	char **argv;
	
	MPI_Init(&argc, &argv);
	MPI_Comm_rank(MPI_COMM_WORLD, &myrank);
}
