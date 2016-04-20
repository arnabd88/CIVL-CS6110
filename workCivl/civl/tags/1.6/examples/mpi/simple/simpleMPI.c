#include<mpi.h>
#include<assert.h>

int myrank;

void main() {
	int argc;
	char **argv;
	double buf = 0.0;
	
	MPI_Init(&argc, &argv);
	MPI_Comm_rank(MPI_COMM_WORLD, &myrank);
	if(myrank == 0) {
		buf = 1.0;
		MPI_Send(&buf, 1, MPI_DOUBLE, 1, 0, MPI_COMM_WORLD);
	} else {
		MPI_Recv(&buf, 1, MPI_DOUBLE, 0, 0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
	}
	assert(buf == 1.0);
	MPI_Finalize();
}
