#include<mpi.h>

/* Only one process inits MPI.  This is OK. */

void main() {
	int argc;
	char **argv;
	
	if (PID == 0) {
		MPI_Init(&argc, &argv);
		MPI_Finalize();
	}
}
