#include <mpi.h>
#include <stdio.h>
#ifdef _CIVL
$input int _mpi_nprocs=5;
#endif
void main(int argc, char * argv[]){

  int nprocs, rank;
  int IntValue;
  double DoubleValue;

  MPI_Init(&argc, &argv);
  MPI_Comm_size(MPI_COMM_WORLD, &nprocs);
  MPI_Comm_rank(MPI_COMM_WORLD, &rank);

  if(nprocs < 2){
    printf("The program needs more than 2 processes.\n");
    MPI_Finalize();
    return;
  }else{
    double temp;

    MPI_Allreduce(&rank, &IntValue, 1, MPI_INT, MPI_SUM, MPI_COMM_WORLD); 
    temp = (double)rank;
    MPI_Reduce(&temp, &DoubleValue, 1, MPI_DOUBLE, MPI_SUM, 0, MPI_COMM_WORLD);
    printf("I'm process %d, my integer value is %d \n", rank, IntValue);
    if(rank == 0)
      printf("I'm process %d, my double value is %.4f \n", rank, DoubleValue);
    MPI_Finalize();
    return;
  }
}
