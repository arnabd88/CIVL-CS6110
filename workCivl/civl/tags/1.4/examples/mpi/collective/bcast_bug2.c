/**
 * This program is written according to the example described in 
 * http://www.mcs.anl.gov/research/projects/mpi/mpi-standard/mpi-report-1.1/node86.htm#Node86
 
 Process zero executes a broadcast, followed by a blocking send operation. Process one first executes a blocking receive that matches the send, followed by broadcast call that matches the broadcast of process zero. This program may deadlock. The broadcast call on process zero may block until process one executes the matching broadcast call, so that the send is not executed. Process one will definitely block on the receive and so, in this case, never executes the broadcast.
 */
#include<stdio.h>
#include<mpi.h>
#include<assert.h>

int main(int argc, char* argv[]){
  int rank;
  int procs;
  int* sendBuf;
  int* rcvBuf;
  int* sum;
  int buf1, buf2;

  MPI_Init(&argc,&argv); 
  MPI_Comm_size(MPI_COMM_WORLD, &procs); 
  MPI_Comm_rank(MPI_COMM_WORLD, &rank); 
  
  if(procs != 2){
    printf("This program requires exactly two processes.\n");
    return 1;
  }

  if(rank == 0){
    buf1=1;
    buf2=2;
  }

  switch(rank) { 
  case 0: 
    MPI_Bcast(&buf1, 1, MPI_INT, 0, MPI_COMM_WORLD); 
    MPI_Send(&buf2, 1, MPI_INT, 1, 0, MPI_COMM_WORLD); 
    break; 
  case 1: 
    MPI_Recv(&buf2, 1, MPI_INT, 0, 0, MPI_COMM_WORLD, MPI_STATUS_IGNORE); 
    MPI_Bcast(&buf1, 1, MPI_INT, 0, MPI_COMM_WORLD); 
    break; 
  } 
  
  printf("process %d: buf1=%d, buf2=%d\n", rank, buf1, buf2);
  assert(buf1==1 && buf2 == 2);
  
  MPI_Finalize();
  return 0;
}
