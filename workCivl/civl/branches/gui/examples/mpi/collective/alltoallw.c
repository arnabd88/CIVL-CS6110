/**
 * This program illustrates MPI_Alltoallv.
 * online source: http://mpi.deino.net/mpi_functions/MPI_Alltoallw.html
 */
#include "mpi.h"
#include <stdlib.h>
#include <stdio.h>
/*
This program tests MPI_Alltoallw by having processor i send different
amounts of data to each processor.
The first test sends i items to processor i from all processors.
*/
int main( int argc, char **argv )
{
    MPI_Comm comm;
    int *sbuf, *rbuf;
    int rank, size;
    int *sendcounts, *recvcounts, *rdispls, *sdispls;
    int i, j, *p, err;
    MPI_Datatype *sendtypes, *recvtypes;

    MPI_Init( &argc, &argv );
    err = 0;
    comm = MPI_COMM_WORLD;
    /* Create the buffer */
    MPI_Comm_size( comm, &size );
    MPI_Comm_rank( comm, &rank );
    sbuf = (int *)malloc( size * size * sizeof(int) );
    rbuf = (int *)malloc( size * size * sizeof(int) );
    if (!sbuf || !rbuf) {
        fprintf( stderr, "Could not allocated buffers!\n" );
        fflush(stderr);
        MPI_Abort( comm, 1 );
    }
    /* Load up the buffers */
    for (i=0; i<size*size; i++) {
        sbuf[i] = i + 100*rank;
        rbuf[i] = -i;
    }
    /* Create and load the arguments to alltoallv */
    sendcounts = (int *)malloc( size * sizeof(int) );
    recvcounts = (int *)malloc( size * sizeof(int) );
    rdispls = (int *)malloc( size * sizeof(int) );
    sdispls = (int *)malloc( size * sizeof(int) );
    sendtypes = (MPI_Datatype *)malloc( size * sizeof(MPI_Datatype) );
    recvtypes = (MPI_Datatype *)malloc( size * sizeof(MPI_Datatype) );
    if (!sendcounts || !recvcounts || !rdispls || !sdispls || !sendtypes || !recvtypes) {
        fprintf( stderr, "Could not allocate arg items!\n" );
        fflush(stderr);
        MPI_Abort( comm, 1 );
    }
    /* Note that process 0 sends no data (sendcounts[0] = 0) */
    for (i=0; i<size; i++) {
        sendcounts[i] = i;
        recvcounts[i] = rank;
        rdispls[i] = i * rank * sizeof(int);
        sdispls[i] = (((i+1) * (i))/2) * sizeof(int);
        sendtypes[i] = recvtypes[i] = MPI_INT;
    }
    MPI_Alltoallw( sbuf, sendcounts, sdispls, sendtypes,
                       rbuf, recvcounts, rdispls, recvtypes, comm );
    /* Check rbuf */
    for (i=0; i<size; i++) {
        p = rbuf + rdispls[i]/sizeof(int);
        for (j=0; j<rank; j++) {
            if (p[j] != i * 100 + (rank*(rank+1))/2 + j) {
                fprintf( stderr, "[%d] got %d expected %d for %dth\n",
                                    rank, p[j],(i*(i+1))/2 + j, j );
                fflush(stderr);
                err++;
            }
        }
    }
    free( sendtypes );
    free( recvtypes );
    free( sdispls );
    free( rdispls );
    free( recvcounts );
    free( sendcounts );
    free( rbuf );
    free( sbuf );
    MPI_Finalize();
    return 0;
}
