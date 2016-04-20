/**
 * This is a simple program to demonstrate the correct usage of two MPI colletive operations,
 * i.e., they have to be executed in the same order for each process.
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
    int* sum;

    MPI_Init(&argc,&argv); 
    MPI_Comm_size(MPI_COMM_WORLD, &procs); 
    MPI_Comm_rank(MPI_COMM_WORLD, &rank); 
    
    if (rank == 0) {
      sendBuf = (int*)malloc(sizeof(int)*procs);
      sum = (int*)malloc(sizeof(int)*procs);
      for(int i=0; i < procs; i++){
	sendBuf[i] = i;
	sum[i] = 0;
      }
    }else{
      sum = (int*)malloc(sizeof(int));
      sendBuf = (int*)malloc(sizeof(int));
    }
    rcvBuf = (int*)malloc(sizeof(int)*procs);

    MPI_Scatter(sendBuf, 1, MPI_INT, rcvBuf, 1, MPI_INT, 0, MPI_COMM_WORLD);

    *sendBuf = *rcvBuf;

    MPI_Allgather(sendBuf, 1, MPI_INT, rcvBuf, 1, MPI_INT, MPI_COMM_WORLD);
    
    printf("Vector of process %d is: (", rank);
    for(int i=0; i<procs; i++){
      printf("%d", rcvBuf[i]);
      if(i != procs-1)
	printf(", ");
      assert(i == rcvBuf[i]);
    }
    printf(")\n");
    
    MPI_Bcast(sum, 1, MPI_INT, 0, MPI_COMM_WORLD);

    MPI_Reduce(rcvBuf, sum, procs, MPI_INT, MPI_SUM, 0, MPI_COMM_WORLD);

    if(rank == 0){
      printf("Vector sum is: (");
      for(int i=0; i<procs; i++){
	printf("%d", sum[i]);
	if(i != procs-1)
	  printf(", ");
	assert(i*procs == sum[i]);
      }
      printf(")\n");
    }
   
    free(sendBuf);
    free(rcvBuf);
    free(sum);
    MPI_Finalize();
    return 0; 
}
