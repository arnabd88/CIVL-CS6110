/* Good scatter.
 */
#include<mpi.h>
#include<assert.h>
#include<stdlib.h>

#define COUNT 10

int nprocs;
int myrank;
int root;

void main() {
  int argc;
  char **argv;
  double *sendbuf = (double*)NULL;
  double recvbuf[COUNT];
  int i;

  MPI_Init(&argc, &argv);
  MPI_Comm_rank(MPI_COMM_WORLD, &myrank);
  MPI_Comm_size(MPI_COMM_WORLD, &nprocs);
  root = nprocs - 1; // to be different
  if (myrank == root) {
    sendbuf = (double*)malloc(COUNT*nprocs*sizeof(double));
    for (i=0; i<COUNT*nprocs; i++)
      sendbuf[i] = 1.0*i;
  }
  MPI_Scatter(sendbuf, COUNT, MPI_DOUBLE, 
	      &recvbuf[0], COUNT, MPI_DOUBLE,
	      root, MPI_COMM_WORLD);
  if (myrank == root) {
    free(sendbuf);
  }
  for (i=0; i<COUNT; i++) {
    assert(recvbuf[i] == COUNT*myrank + i);
  }
  MPI_Finalize();
}
