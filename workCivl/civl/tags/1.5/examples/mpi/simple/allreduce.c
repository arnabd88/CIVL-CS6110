/* Good broadcasts.
 */
#include<mpi.h>
#include<assert.h>

int nprocs;
int myrank;

#define count 10

void main() {
  int argc;
  char **argv;
  double x[count];
  double y[count];
  int i;
    
  MPI_Init(&argc, &argv);
  MPI_Comm_rank(MPI_COMM_WORLD, &myrank);
  MPI_Comm_size(MPI_COMM_WORLD, &nprocs);
  for (i=0; i<count; i++)
    x[i]=myrank;
  MPI_Allreduce(&x[0], &y[0], count, MPI_DOUBLE, MPI_SUM, MPI_COMM_WORLD);
  for (i=0; i<count; i++)
    assert(x[i]==myrank);
  for (i=0; i<count; i++)
    assert(y[i]==nprocs*(nprocs-1)/2);
  MPI_Finalize();
}
