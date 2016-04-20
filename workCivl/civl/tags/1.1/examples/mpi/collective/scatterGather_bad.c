/**
 * This program has a deadlock because processes dont execute MPI_Scatter 
 * and MPI_Gather in the same order.
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
      rcvBuf = (int*)malloc(sizeof(int)*procs);
      for(int i=0; i < procs; i++)
	sendBuf[i] = i;
    }else{
      sendBuf = (int*)malloc(sizeof(int));
      rcvBuf = (int*)malloc(sizeof(int));
    }

    if(rank%2)
      MPI_Scatter(sendBuf, 1, MPI_INT, rcvBuf, 1, MPI_INT, 0, MPI_COMM_WORLD);
    else
      MPI_Gather(sendBuf, 1, MPI_INT, rcvBuf, 1, MPI_INT, 0, MPI_COMM_WORLD);
    
    if(rank%2)
      MPI_Gather(sendBuf, 1, MPI_INT, rcvBuf, 1, MPI_INT, 0, MPI_COMM_WORLD);
    else
      MPI_Scatter(sendBuf, 1, MPI_INT, rcvBuf, 1, MPI_INT, 0, MPI_COMM_WORLD);

    if(rank == 0){
      for(int i=0; i<procs; i++){
	printf("sendBuf[%d]=%d, rcvBuf[%d]=%d\n", i, sendBuf[i], i, rcvBuf[i]);
	assert(sendBuf[i] == rcvBuf[i]);
      }
    }
    
    free(sendBuf);
    free(rcvBuf);
    return 0; 
}
