#include "mpi.h"
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#define SIZE 4

int main (int argc, char *argv[])
{
  int numtasks, rank, sendcount, recvcount, source;
  float sendbuf[SIZE * SIZE] = {
    1.0, 2.0, 3.0, 4.0,
    5.0, 6.0, 7.0, 8.0,
    9.0, 10.0, 11.0, 12.0,
    13.0, 14.0, 15.0, 16.0};
  float recvbuf[SIZE];
  
  MPI_Init(&argc,&argv);
  MPI_Comm_rank(MPI_COMM_WORLD, &rank);
  MPI_Comm_size(MPI_COMM_WORLD, &numtasks);

  if (numtasks == SIZE) {
    source = 1;
    sendcount = SIZE;
    recvcount = SIZE;
    if(source == rank){
      // Locally assign recvbuf for root process,
      // then using MPI_INPLACE for scattring.
      for(int i=0; i<SIZE; i++)
	recvbuf[i] = *(sendbuf + rank * SIZE + i);
      MPI_Scatter(sendbuf,sendcount,MPI_FLOAT,MPI_IN_PLACE,recvcount,
		  MPI_FLOAT,source,MPI_COMM_WORLD);
    }
    else
      MPI_Scatter(sendbuf,sendcount,MPI_FLOAT,recvbuf,recvcount,
		  MPI_FLOAT,source,MPI_COMM_WORLD);
    
    printf("rank= %d  Results: %f %f %f %f\n",rank,recvbuf[0],
	   recvbuf[1],recvbuf[2],recvbuf[3]);
    //add assertions
    for(int i=0; i<SIZE; i++)
      assert(recvbuf[i] == *(sendbuf + SIZE * rank + i));
  }
  else
    printf("Must specify %d processors. Terminating.\n",SIZE);
  
  MPI_Finalize();
}
