/* Run the program with 2 processes: mpiexec -n 2 a.out */

#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>
#include "mpi.h"

int rank;

void *run_test(void * arg)
{
    MPI_Status  reqstat;
    int i, j, x, y;
    int peer = rank ? 0 : 1;

    for (j = 0; j < 2; j++) {
	if (rank % 2) {
	    for (i = 0; i < 3; i++)
		MPI_Send(&x, 0, MPI_CHAR, peer, 0, MPI_COMM_WORLD);
	    for (i = 0; i < 3; i++)
		MPI_Recv(&y, 0, MPI_CHAR, peer, 0, MPI_COMM_WORLD, &reqstat);
	}
	else {
	    for (i = 0; i < 3; i++)
		MPI_Recv(&y, 0, MPI_CHAR, peer, 0, MPI_COMM_WORLD, &reqstat);
	    for (i = 0; i < 3; i++)
		MPI_Send(&x, 0, MPI_CHAR, peer, 0, MPI_COMM_WORLD);
	}
    }
    return 0;
}

int main(int argc, char ** argv)
{
    pthread_t thread;
    int i, zero = 0, pmode, nprocs;

    MPI_Init_thread(&argc, &argv, MPI_THREAD_MULTIPLE, &pmode);
    if (pmode != MPI_THREAD_MULTIPLE) {
	fprintf(stderr, "Thread Multiple not supported by the MPI implementation\n");
	MPI_Abort(MPI_COMM_WORLD, -1);
    }

    MPI_Comm_size(MPI_COMM_WORLD, &nprocs);
    MPI_Comm_rank(MPI_COMM_WORLD, &rank);

    if (nprocs != 2) {
	fprintf(stderr, "Need two processes\n");
	MPI_Abort(MPI_COMM_WORLD, -1);
    }

    pthread_create(&thread, NULL, run_test, NULL);
    run_test(&zero);
    pthread_join(thread, NULL);

    MPI_Finalize();

    return 0;
}
