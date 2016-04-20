#include<mpi.h>
#include<assert.h>

int nprocs;
int myrank;

void main() {
	int argc;
	char **argv;
	double x;
	MPI_Status status;
	
	MPI_Init(&argc, &argv);
	MPI_Comm_rank(MPI_COMM_WORLD, &myrank);
	if (myrank == 0) {
		MPI_Recv(&x, 1, MPI_DOUBLE, MPI_ANY_SOURCE, MPI_ANY_TAG, MPI_COMM_WORLD, &status);
		assert(x == (double)(status.MPI_SOURCE));
		assert(status.MPI_TAG == 10+status.MPI_SOURCE);
	} else {
		x = (double)myrank;
		MPI_Send(&x, 1, MPI_DOUBLE, 0, myrank+10, MPI_COMM_WORLD);
	}
	MPI_Finalize();
}
