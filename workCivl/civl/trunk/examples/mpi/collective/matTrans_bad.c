/**
 * This exercise presents a simple program to demonstrate the use of MPI_Alltoall. 
 * In this exercise, a 4x4 matrix has been divided into 4 1x4 submatrices. 
 * Each submatrix is stored in the local memory of each process. 
 * Using MPI_Alltoall, each element j of submtarix in process i is replaced by element i 
 * of submatrix in process j. A few bugs have been delibrately introduced into the given program. 
 * Based on our discussion of MPI_Alltoall, can you find the bugs and correct them?
 *
 * online source: http://static.msi.umn.edu/tutorial/scicomp/general/MPI/workshop_MPI/src/alltoall/main.html
 */

#include <stdio.h>
#include "mpi.h"

int main( int argc, char **argv )
{
    int send[4], recv[3];
    int rank, size, k;
    
    MPI_Init( &argc, &argv );
    MPI_Comm_rank( MPI_COMM_WORLD, &rank );
    MPI_Comm_size( MPI_COMM_WORLD, &size );
    
    if (size != 4) {
        printf("Error!:# of processors must be equal to 4\n");
        printf("Programm aborting....\n");
        MPI_Abort(MPI_COMM_WORLD, 1);
    }
    for (k=0;k<size;k++) send[k] = (k+1) + rank*size;
    
    printf("%d : send = %d %d %d %d\n", rank, send[0], send[1], send[2], send[3]);
    
    MPI_Alltoall(&send, 2, MPI_FLOAT, &recv, 1, MPI_INT, MPI_COMM_WORLD);
    
    printf("%d : recv = %d %d %d %d\n", rank, recv[0], recv[1], recv[2], recv[3]);
    
    MPI_Finalize();
    return 0;
}
