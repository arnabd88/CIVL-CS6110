/**
 * This example has a deadlock because collective operations are not called in the same
 * order for all processes.
 */

#include<mpi.h>
#include<stdlib.h>
#include<assert.h>
#include<stdio.h>

int main(int argc, char * argv[]) 
{ 
    int rank;
    int procs;
    int* sendBuf;
    int* rcvBuf;

    MPI_Init(&argc,&argv); 
    MPI_Comm_size(MPI_COMM_WORLD, &procs); 
    MPI_Comm_rank(MPI_COMM_WORLD, &rank); 
    
    if (rank == 0) {
      sendBuf = (int*)malloc(sizeof(int)*procs);
      //rcvBuf = (int*)malloc(sizeof(int)*procs);
      for(int i=0; i < procs; i++)
	sendBuf[i] = i;
    }else{
      sendBuf = (int*)malloc(sizeof(int));
    }
    rcvBuf = (int*)malloc(sizeof(int)*procs);

    if(rank%2)
      MPI_Scatter(sendBuf, 1, MPI_INT, rcvBuf, 1, MPI_INT, 0, MPI_COMM_WORLD);
    else
      MPI_Allgather(sendBuf, 1, MPI_INT, rcvBuf, 1, MPI_INT, MPI_COMM_WORLD);

    *sendBuf = *rcvBuf + rank;

    if(rank%2)
      MPI_Allgather(sendBuf, 1, MPI_INT, rcvBuf, 1, MPI_INT, MPI_COMM_WORLD);
    else
      MPI_Scatter(sendBuf, 1, MPI_INT, rcvBuf, 1, MPI_INT, 0, MPI_COMM_WORLD);

    printf("receive buffer of process %d:\n", rank);
    for(int i=0; i<procs; i++){
      printf("rcvBuf[%d]=%d\n", i, rcvBuf[i]);
      assert(i*2 == rcvBuf[i]);
    }
    free(sendBuf);
    free(rcvBuf);
    return 0; 
}
