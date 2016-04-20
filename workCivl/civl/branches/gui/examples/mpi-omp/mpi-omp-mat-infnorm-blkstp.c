#ifdef _CIVL
#include <civlc.cvh>
#endif
/*************************************************************************
              C-DAC Tech Workshop : HeGaPa-2012
                     July 16-20,2012

  Example 3     :   Mpi-Omp_MatInf_blkstp.c
 
  Objective     :   Write parallel program using MPI and OPENMP to compute norm
                    of a square matrix.
  
  Input         :   Read file (infndata.inp) for Matrix
  
  Output        :   Process with rank 0 prints the value of Infinity Norm
  
  Created       : MAY-2012    

************************************************************************/

#include <stdio.h>
#include <stdlib.h>
#include "mpi.h"
#include <omp.h>

#ifdef _CIVL
$input int NUM_ROWS_BOUND = 4;
$input int NUM_COLS_BOUND = 4;
#endif

/* Main Program */

int main(int argc, char **argv) // "int" inserted manually
//main(int argc, char **argv)
{

  int             Numprocs, MyRank, iam;
  int             NoofCols, NoofRows, ScatterSize;
  int             index, irow, icol;
  int             Root = 0;
  float         **InputMatrix, *Buffer, *MyBuffer;
  float           max = 0, sum = 0, Inf_norm = 0;
  FILE           *fp;
  int             MatrixFileStatus = 1;

  /* ........MPI Initialisation ....... */

  MPI_Init(&argc, &argv);
  MPI_Comm_rank(MPI_COMM_WORLD, &MyRank);
  MPI_Comm_size(MPI_COMM_WORLD, &Numprocs);

  if (MyRank == 0) {

    /* .......Read The Matrix Input File ...... */
    if ((fp = fopen("./data/infndata.inp", "r")) == NULL) {
      MatrixFileStatus = 0;
    }
    if (MatrixFileStatus != 0) {
      fscanf(fp, "%d %d\n", &NoofRows, &NoofCols);

      #ifdef _CIVL
      $assume(NoofRows <= NUM_ROWS_BOUND);
      $assume(NoofRows <= NoofCols);
      #endif

      /* .......Allocate Memory For Matrix ..... */
      InputMatrix = (float **) malloc(NoofRows * sizeof(float *));
      for (irow = 0; irow < NoofRows; irow++)
	InputMatrix[irow] = (float *) malloc(NoofCols * sizeof(float));

      /* .......Read Data For Matrix ..... */
      for (irow = 0; irow < NoofRows; irow++) {
	for (icol = 0; icol < NoofCols; icol++)
	  fscanf(fp, "%f", &InputMatrix[irow][icol]);
      }
      fclose(fp);

      /*
       * .......Convert 2-D InputMatrix Into 1-D Array
       * .....
       */
      Buffer = (float *) malloc(NoofRows * NoofCols * sizeof(float));

      index = 0;
      for (irow = 0; irow < NoofRows; irow++) {
	for (icol = 0; icol < NoofCols; icol++) {
	  Buffer[index] = InputMatrix[irow][icol];
	  index++;
	}
      }
    }
  }/* MyRank == 0 */
  MPI_Barrier(MPI_COMM_WORLD);
  MPI_Bcast(&MatrixFileStatus, 1, MPI_INT, Root, MPI_COMM_WORLD);
  if (MatrixFileStatus == 0) {
    if (MyRank == Root)
      printf("Can't Open Matrix Input File");
    MPI_Finalize();
    exit(-1);
  }
  MPI_Bcast(&NoofRows, 1, MPI_INT, Root, MPI_COMM_WORLD);

  #ifdef _CIVL
  $assume(NoofRows >= Numprocs);
  #endif
  if (NoofRows < Numprocs) {
    MPI_Finalize();
    if (MyRank == 0)
      printf("Noof Rows Should Be More Than No of Processors ... \n");
    exit(0);
  }
  #ifdef _CIVL
  $assume(NoofRows % Numprocs == 0);
  #endif
  if (NoofRows % Numprocs != 0) {
    MPI_Finalize();
    if (MyRank == 0) {
      printf("Matrix Cannot Be Striped Evenly ..... \n");
    }
    exit(0);
  }
  MPI_Bcast(&NoofCols, 1, MPI_INT, Root, MPI_COMM_WORLD);

  ScatterSize = NoofRows / Numprocs;
  MyBuffer = (float *) malloc(ScatterSize * NoofCols * sizeof(float));
  MPI_Scatter(Buffer, ScatterSize * NoofCols, MPI_FLOAT,
	      MyBuffer, ScatterSize * NoofCols, MPI_FLOAT,
	      0, MPI_COMM_WORLD);

  /* OpenMP Parallel Directive */

  max = 0;
  /*
#pragma omp parallel private(iam) shared(max)
{
iam = omp_get_thread_num();
printf("The Threadid Is %d With each Processor's Rank %d\n", iam, MyRank);

OpenMP Parallel For Directive 
  */
  omp_set_num_threads(4);
#pragma omp parallel for private(sum,index,icol) shared(max)
 for (irow = 0; irow < ScatterSize; irow++) {
   printf("The Threadid Is %d With each Processor's Rank %d\n",omp_get_thread_num(), MyRank);
   sum = 0;
   index = irow * NoofCols;
   for (icol = 0; icol < NoofCols; icol++) {
     sum += (MyBuffer[index] >= 0) ? (MyBuffer[index]) : (0 - MyBuffer[index]);
     index++;
   }

   /* OpenMP Critical Section */

#pragma omp critical
   if (sum > max)
     max = sum;
 }

 MPI_Barrier(MPI_COMM_WORLD);
 MPI_Reduce(&max, &Inf_norm, 1, MPI_DOUBLE, MPI_MAX, 0, MPI_COMM_WORLD);
 if (MyRank == 0) {
   max = 0;

   /* Serial Check */

   for (irow = 0; irow < NoofRows; irow++) {
     sum = 0;
     index = irow * NoofCols;
     for (icol = 0; icol < NoofCols; icol++) {
       sum += (Buffer[index] >= 0) ? (Buffer[index]) : (0 - Buffer[index]);
       index++;
     }
     max = max < sum ? sum : max;
   }

   printf("\nThe Infinity Norm Is(Parallel Code) : %f\n", Inf_norm);
   printf("\nThe Infinity Norm Is(Serial Code)   : %f\n\n", max);

   /* Freeing Allocated Memory */
   
   free(InputMatrix);
   free(Buffer);
 }
 /* MPI-Termination */

 free(MyBuffer);

 MPI_Finalize();
}

