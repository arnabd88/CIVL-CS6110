#include <mpi.h>
#include <civlmpi.cvh>
#include <assert.h>

#ifdef _CIVL
$input int _NPROCS_LOWER_BOUND = 1;
$input int _NPROCS_UPPER_BOUND = 6;
#endif

int main(int argc, char * argv[]) {
  __MPI_Sys_status__ curr_status;

  MPI_Init(&argc, &argv);
#ifdef _CIVL
  curr_status = CMPI_Get_status();
  $assert __INIT == curr_status;
#endif
  MPI_Finalize();
}
