/* Good broadcast followed by gather.
 */
#include<mpi.h>
#include<assert.h>
#include<stdlib.h>

#define COUNT 5
#ifdef _CIVL
$input double a[COUNT];
#else
double a[COUNT];
#endif
double buf1[COUNT];
double *buf2;
int nprocs;
int rank;

void main() {
  int argc;
  char **argv;
  int i;
  
  MPI_Init(&argc, &argv);
  MPI_Comm_rank(MPI_COMM_WORLD, &rank);
  MPI_Comm_size(MPI_COMM_WORLD, &nprocs);
  if (rank == 0) {
    for (i=0; i<COUNT; i++)
      buf1[i] = a[i];
  }
  MPI_Bcast(&buf1[0], COUNT, MPI_DOUBLE, 0, MPI_COMM_WORLD);
  if (rank == 1)
    buf2 = (double*)malloc(nprocs*COUNT*sizeof(double));
  else
    buf2= (double*)NULL;
  MPI_Gather(&buf1[0], COUNT, MPI_DOUBLE,
	     buf2, COUNT, MPI_DOUBLE,
	     1, MPI_COMM_WORLD);
  if (rank == 1) {
    for (i=0; i<nprocs*COUNT; i++)
      assert(buf2[i]==a[i%COUNT]);
    free(buf2);
  }
  MPI_Finalize();
}
