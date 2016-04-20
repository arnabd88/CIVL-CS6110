#ifdef _CIVL
#include <civlc.cvh>
#endif
#include <mpi.h>
#include <civl-mpi.cvh>
#include <assert.h>

#ifdef _CIVL
$input int _mpi_nprocs_lo = 1;
$input int _mpi_nprocs_hi = 6;
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
