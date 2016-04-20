#include <stdio.h>
#include <stdlib.h>
#include "mpi.h"

/**
 * This example demonstrates the usage of MPI collective operations,
 * which should be called in the same orders for all MPI processes.
 * This example has an error when there are more than five MPI processes.
 */
#include<mpi.h>

int main(int argc, char *argv[]) {
    int rank, size, i, n;

    MPI_Init(&argc, &argv);
    MPI_Comm_rank(MPI_COMM_WORLD, &rank);
    MPI_Comm_size(MPI_COMM_WORLD, &size);

    int sendbuf[size];
    int recvbuf;

    if(rank == 0){
      for (int i=0; i<size; i++)
	sendbuf[i] = 1 + rank + size*i;
    }
    
    if(rank != 6)
      MPI_Bcast(sendbuf, size, MPI_INT, 0, MPI_COMM_WORLD);

    printf("Proc %d: ", rank);
    for (int i=0; i<size; i++) printf("%d ", sendbuf[i]);
    printf("\n");

    int recvcounts[size];
    for (int i=0; i<size; i++)
        recvcounts[i] = 1;

    MPI_Reduce_scatter(sendbuf, &recvbuf, recvcounts, MPI_INT, MPI_MAX, MPI_COMM_WORLD);

    printf("Proc %d: %d\n", rank, recvbuf);

    MPI_Finalize();

    return 0;
}
