#ifdef _CIVL
#include <civlc.cvh>
#endif
#include <mpi.h>
#include <civl-mpi.cvh>
#include <assert.h>

#ifdef _CIVL
$input int _NPROCS_LOWER_BOUND = 1;
$input int _NPROCS_UPPER_BOUND = 6;
#endif

int main(int argc, char * argv[]) {
  $mpi_sys_status curr_status;

  MPI_Init(&argc, &argv);
#ifdef _CIVL
  curr_status = $mpi_get_status();
  $assert(__INIT == curr_status);
#endif
  MPI_Finalize();
}
