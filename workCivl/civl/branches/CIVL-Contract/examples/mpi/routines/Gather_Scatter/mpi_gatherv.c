#include <mpi.h>
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#define SIZE 4

int main (int argc, char *argv[])
{
  int numtasks, rank, source;
  int sendcounts[4] = {2, 4, 5, 5};
  int recvcounts[4] = {2, 4, 5, 5};
  int displs[4] = {0, 2, 6, 11};
  float recvbuf[SIZE * SIZE];
  float * sendbuf;
  
  MPI_Init(&argc,&argv);
  MPI_Comm_rank(MPI_COMM_WORLD, &rank);
  MPI_Comm_size(MPI_COMM_WORLD, &numtasks);

  sendbuf = malloc(sizeof(float) * sendcounts[rank]);
  if (numtasks == SIZE) {
    source = 1;
    //init sendbuf
    for(int i=0; i<sendcounts[rank]; i++)
      sendbuf[i] = (float)(displs[rank] + i);
    MPI_Gatherv(sendbuf,sendcounts[rank],MPI_FLOAT,recvbuf, recvcounts, displs,
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
  free(sendbuf);
}
