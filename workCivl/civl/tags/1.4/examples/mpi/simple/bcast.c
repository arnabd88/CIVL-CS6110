/* Good broadcasts.
 */
#include<mpi.h>
#include<assert.h>

int nprocs;
int myrank;

void main() {
  int argc;
  char **argv;
  double x;
  double y;
    
  MPI_Init(&argc, &argv);
  MPI_Comm_rank(MPI_COMM_WORLD, &myrank);
  x=myrank;
  y=myrank;
  MPI_Bcast(&x, 1, MPI_DOUBLE, 0, MPI_COMM_WORLD);
  MPI_Bcast(&y, 1, MPI_DOUBLE, 1, MPI_COMM_WORLD);
  assert(x==0);
  assert(y==1);
  MPI_Finalize();
}
