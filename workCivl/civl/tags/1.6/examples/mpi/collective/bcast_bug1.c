/**
 * This program is written according to the example described in 
 * http://www.mcs.anl.gov/research/projects/mpi/mpi-standard/mpi-report-1.1/node86.htm#Node86
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

  buf1=rank;
  buf2=rank;

  switch(rank){
  case 0:
    MPI_Bcast(&buf1, 1, MPI_INT, 0, MPI_COMM_WORLD);
    MPI_Bcast(&buf2, 1, MPI_INT, 1, MPI_COMM_WORLD);
    break;
  case 1:
    MPI_Bcast(&buf2, 1, MPI_INT, 1, MPI_COMM_WORLD);
    MPI_Bcast(&buf1, 1, MPI_INT, 0, MPI_COMM_WORLD);
    break;
  }
  
  printf("process %d: buf1=%d, buf2=%d\n", rank, buf1, buf2);
  assert(buf1==0 && buf2 == 1);
  
  MPI_Finalize();
  return 0;
}
