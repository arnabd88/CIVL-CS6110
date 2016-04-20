/* Good Allgather.
 */
#include<mpi.h>
#include<assert.h>
#include<stdlib.h>

#define COUNT 10

int nprocs;
int myrank;

void main() {
  int argc;
  char **argv;
  double *recvbuf = (double*)NULL;
  double sendbuf[COUNT];
  int i;

  MPI_Init(&argc, &argv);
  MPI_Comm_rank(MPI_COMM_WORLD, &myrank);
  MPI_Comm_size(MPI_COMM_WORLD, &nprocs);
  for (i=0; i<COUNT; i++)
    sendbuf[i]=myrank*COUNT+i;
  recvbuf = (double*)malloc(COUNT*nprocs*sizeof(double));
  MPI_Allgather(&sendbuf[0], COUNT, MPI_DOUBLE, 
		recvbuf, COUNT, MPI_DOUBLE,
		MPI_COMM_WORLD);
  for (i=0; i<nprocs*COUNT; i++) {
    assert(recvbuf[i] == 1.0*i);
  }
  free(recvbuf);
  MPI_Finalize();
}
