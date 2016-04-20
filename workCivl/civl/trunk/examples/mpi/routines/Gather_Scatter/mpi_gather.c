#include <mpi.h>
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#define SIZE 4

int main (int argc, char *argv[])
{
  int numtasks, rank, sendcount, recvcount, source;
  float sendbuf[SIZE];
  float recvbuf[SIZE * SIZE];
  
  MPI_Init(&argc,&argv);
  MPI_Comm_rank(MPI_COMM_WORLD, &rank);
  MPI_Comm_size(MPI_COMM_WORLD, &numtasks);

  if (numtasks == SIZE) {
    source = 1;
    sendcount = SIZE;
    recvcount = SIZE;
    //init sendbuf
    for(int i=0; i<SIZE; i++)
      sendbuf[i] = (float)(rank * SIZE + i);
    MPI_Gather(sendbuf,sendcount,MPI_FLOAT,recvbuf,recvcount,
	       MPI_FLOAT,source,MPI_COMM_WORLD);
    //assertions
    if(rank == source){
      for(int i=0; i<(SIZE*SIZE); i++){
	printf("recvbuf[%d] : %f\n", i, recvbuf[i]);
	assert(recvbuf[i] == i);
      }
    }
  }
  else
    printf("Must specify %d processors. Terminating.\n",SIZE);
  
  MPI_Finalize();
}
