#include<mpi.h>
int shared;
/*@
  @ requires x == \mpi_comm_rank;
  @ ensures  (\mpi_empty_in(0)) && (\mpi_empty_out(0));
  @ \mpi_collective(MPI_COMM_WORLD, COL): 
  @     ensures \mpi_comm_size == 9;
  @     behavior name:
  @       ensures \mpi_comm_size == 9;
  @*/
int foo(int x) {
  return x;
}

int main() {

  return 0;
}
