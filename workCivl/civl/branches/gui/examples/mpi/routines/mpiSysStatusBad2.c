#include <mpi.h>

#ifdef _CIVL
$input int _mpi_nprocs = 2;
#endif

int main(int argc, char * argv[]) {
  int rank;

  MPI_Init(&argc, &argv);
  MPI_Finalize();
  MPI_Comm_rank(MPI_COMM_WORLD, &rank);
}
