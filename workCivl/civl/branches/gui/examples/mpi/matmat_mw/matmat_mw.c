/* matmat_mw.c : parallel multiplication of two matrices.
 * To execute: mpicc matmat_mw.c ; mpiexec -n 4 ./a.out N L M
 * Or replace "4" with however many procs you want to use.
 * Arguments N L M should be replaced with any integer numbers which is 
 * no larger than the corresponding dimension decided in the "data" file.
 * To verify: civl verify matmat_mw.c
 */
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <mpi.h>

#define comm MPI_COMM_WORLD
#ifdef _CIVL
#include <civlc.cvh>
$input int _mpi_nprocs_lo = 2;
$input int _mpi_nprocs_hi = 4;
/* Dimensions of 2 matrices: a[N][L] * b[L][M] */
$input int NB = 3;              // upper bound of N
$input int N;
$assume(0 < N && N <= NB);
$input int LB = 3;              // upper bound of L
$input int L;
$assume(0 < L && L <= LB);
$input int MB = 3;              // upper bound of M
$input int M;
$assume(0 < M && M <= MB);
$input double a[N][L];          // input data for matrix a
$input double b[L][M];          // input data for matrix b
double oracle[N][M];            // matrix stores results of a sequential run
#else
FILE * fp;                      // pointer to the data file which gives two matrices
int N, L, M;
#endif

/* prints a matrix. In CIVL mode, it will compare the matrix with the
   result of the sequential run.*/
void printMatrix(int numRows, int numCols, double *m) {
  int i, j;

  for (i = 0; i < numRows; i++) {
    for (j = 0; j < numCols; j++) {
      printf("%f ", m[i*numCols + j]);
#ifdef _CIVL
      $assert(m[i*numCols + j] == oracle[i][j], "The calculated value at position [%d][%d] is %f"
	" but the expected one is %f", i, j, m[i*numCols+j], oracle[i][j]);
#endif
    }
    printf("\n");
  }
  printf("\n");
}

/* Computes a vetor with length L times a matrix with dimensions [L][M] */
void vecmat(double vector[L], double matrix[L][M], double result[M]) {
  int j, k;

  for (j = 0; j < M; j++)
    for (k = 0, result[j] = 0.0; k < L; k++)
      result[j] += vector[k]*matrix[k][j];
}

int main(int argc, char *argv[]) {
  int rank, nprocs, i, j;
  MPI_Status status;
  
#ifndef _CIVL
  N = atoi(argv[1]);
  L = atoi(argv[2]);
  M = atoi(argv[3]);
#endif
  MPI_Init(&argc, &argv);
  MPI_Comm_rank(comm, &rank);
  MPI_Comm_size(comm, &nprocs);
  if (rank == 0) {
    double c[N][M], tmp[M];
    int count;
#ifndef _CIVL
    double a[N][L], b[L][M];

    fp = fopen("data", "r");
    for (i = 0; i < N; i++)
      for (j = 0; j < L; j++)
	fscanf(fp,"%lf", &a[i][j]);
    for (i = 0; i < L; i++)
      for (j = 0; j < M; j++)
	fscanf(fp,"%lf",&b[i][j]);
#else
    // elaborating N, L, M....
    //$elaborate(N);
    //$elaborate(L);
    //$elaborate(M);
    // sequential run
    for(int i=0; i < N; i++) {
      vecmat(a[i], b, &oracle[i][0]);
  }

#endif
    MPI_Bcast(b, L*M, MPI_DOUBLE, 0, comm);
    for (count = 0; count < nprocs-1 && count < N; count++)
      MPI_Send(&a[count][0], L, MPI_DOUBLE, count+1, count+1, comm);
    for (i = 0; i < N; i++) {
      MPI_Recv(tmp, M, MPI_DOUBLE, MPI_ANY_SOURCE, MPI_ANY_TAG, comm, &status);
      for (j = 0; j < M; j++) c[status.MPI_TAG-1][j] = tmp[j];
      if (count < N) {
	MPI_Send(&a[count][0], L, MPI_DOUBLE, status.MPI_SOURCE, count+1, comm);
	count++;
      }
    }
    for (i = 1; i < nprocs; i++) MPI_Send(NULL, 0, MPI_INT, i, 0, comm);
    printMatrix(N, M, &c[0][0]);
#ifndef _CIVL
    fclose(fp);
#endif
  } else {
    double b[L][M], in[L], out[M];

    MPI_Bcast(b, L*M, MPI_DOUBLE, 0, comm);
    while (1) {
      MPI_Recv(in, L, MPI_DOUBLE, 0, MPI_ANY_TAG, comm, &status);
      if (status.MPI_TAG == 0) break;
      vecmat(in, b, out);
      MPI_Send(out, M, MPI_DOUBLE, 0, status.MPI_TAG, comm);
    }
  }
  MPI_Finalize();
  return 0;
}

