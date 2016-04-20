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
  float sendbuf[SIZE * SIZE] = {0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15};
  float * recvbuf;
  
  MPI_Init(&argc,&argv);
  MPI_Comm_rank(MPI_COMM_WORLD, &rank);
  MPI_Comm_size(MPI_COMM_WORLD, &numtasks);

  recvbuf = malloc(sizeof(float) * recvcounts[rank]);
  if (numtasks == SIZE) {
    source = 1;
    MPI_Scatterv(sendbuf, sendcounts, displs, MPI_FLOAT, recvbuf, recvcounts[rank],
	       MPI_FLOAT, source, MPI_COMM_WORLD);
    //assertions
    for(int i=0; i<recvcounts[rank]; i++){
      printf("process:%d recvbuf[%d] : %f\n", rank, i, recvbuf[i]);
      assert(recvbuf[i] == displs[rank] + i);
    }
  }
  else
    printf("Must specify %d processors. Terminating.\n",SIZE);
  
  MPI_Finalize();
  free(recvbuf);
}
