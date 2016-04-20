#ifdef _CIVL
#include <civlc.cvh>
#endif
/* FILE: gaussJordan_elimination.c A gaussian-jordan elimination
 * solver that converts a given matrix to a reduce row echelon form
 * matrix
 * RUN : mpicc gaussJordan_elimination.c; mpiexec -n 4 ./a.out numRow numCol m[0][0], m[0][1] ...
 * VERIFY : civl verify gaussianJordan_elimination.c
 */
#include <assert.h>
#include <mpi.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* Message tag */
#define PRINT 0
/* Global parameters */
#ifdef _CIVL
$input int _mpi_nprocs_hi=3;  
$input int _mpi_nprocs_lo=1;   
$input int ROWB = 3;                      // upper bound of numRow
$input int numRow;                        // number of rows in the matrix
$assume(0 < numRow && numRow <= ROWB);
$input int COLB = 3;                      // upper bound of numCol
$input int numCol;                        // number of columns in the matrix
$assume(0 < numCol && numCol <= COLB);
$input long double data[numRow][numCol];  // input matrix
long double oracle[numRow][numCol];       // results of sequential run
#else
int numRow;     // number of rows in the matrix
int numCol;     // number of columns in the matrix, the right-most
		// column is vector B
#endif
int localRow;   // number of rows owned by the process
int rank, nprocs;
int first;      // the global index of the first row in original 
                // matrix
/* a Global Row Index -> Current Row Location table maps original
   indices of rows to their current location in current matrix */
int *loc;       
/* a Current Row Location -> Global Row Index table maps current
   locations of current matrix to their original row indices */
int *idx;

/* Book keeping functions */
/* Return the owner of the row given by the global index of it in
   original matrix */
#define OWNER(index) ((nprocs*(index+1)-1)/numRow)

/* Returns the global index of the first row owned
 * by the process with given rank */
int firstForProc(int rank) {
  return (rank*numRow)/nprocs;      
}

/* Returns the number of rows the given process owns */
int countForProc(int rank) {
  int a = firstForProc(rank);
  int b = firstForProc(rank + 1);

  return b - a;
}

/* Locally print a row */
void printRow(long double * row) {
  for(int k=0; k < numCol; k++)
    printf("%2.6Lf ", row[k]);
  printf("\n");
}

/* Print the given matrix. Since each process needs to send their data
 * to root process 0, this function is collective.
 * Parameters: 
 * a: the (part of) matrix will be printed.  
 */
void printSystem(long double * a) {
  long double recvbuf[numCol];
  
  // Every process follows the order of locations of rows to send their
  // rows to process with rank 0
  for(int i=0; i<numRow; i++)
    if(OWNER(idx[i]) == rank && rank != 0) 
      MPI_Send(&a[(idx[i]-first)*numCol], numCol, MPI_LONG_DOUBLE, 0, i, MPI_COMM_WORLD);
  
  if(rank == 0) {
    for(int i=0; i<numRow; i++) {
      if(OWNER(idx[i]) != 0) {
	MPI_Recv(recvbuf, numCol, MPI_LONG_DOUBLE, MPI_ANY_SOURCE, i, 
		 MPI_COMM_WORLD, MPI_STATUS_IGNORE);
	printRow(recvbuf);
#ifdef _CIVL
	for(int j=0; j < numCol; j++) {
	$assert((recvbuf[j] == oracle[i][j]), "Get %Lf while expecting %Lf at position [%d][%d]\n", recvbuf[j], oracle[i][j], i, j);
	}
#endif
      }
      else {
	printRow(&a[(idx[i]-first)*numCol]);
#ifdef _CIVL
	for(int j=0; j < numCol; j++) {
	$assert((a[(idx[i]-first)*numCol + j] == oracle[i][j]), "Get %Lf while expecting %Lf at position [%d][%d]\n", 
	    a[(idx[i]-first)*numCol + j], oracle[i][j], i, j);
	}
#endif
      }
    }
  }
}

void specElimination(long double *a, int * rowLoc) {
  long double denom;      // a temporary variable will be used to
                          //divide other variables

  for(int i=0; i < numRow; i++) {
    int leadCol = numCol; // the column where leading 1  be in
    int rowOfLeadCol = i; // the row where leadCol be in

    /* step 1: Find out the leftmost nonzero column, interchange it with
     the current iterated row. */
    for(int j=i; j < numCol; j++) {
      for(int k=i; k < numRow; k++) {
	if(a[rowLoc[k]*numCol + j] != 0.0) {
	  leadCol = j;
	  rowOfLeadCol = k;
	  break;
	}
      }
      if(leadCol < numCol) 
	break;
    }
    /* If there is no leading 1 in all unprocessed rows, elimination
       terminates. */
    if(leadCol == numCol)
      return;
    /* step 2: Reducing the leading number to one */
    denom = a[rowLoc[rowOfLeadCol]*numCol + leadCol];
    /* If the denominator is zero (or extremely nearing zero), do
     * nothing.  The reason is the denominator is the left-most
     * nonzero element in all unprocessed rows, if it's zero, all
     * numbers at that column in all unprocessed rows are zeros. For
     * such a case, it's no need to do anything in this iteration.
     */
    if(denom != 0.0) {
      for(int j=leadCol; j < numCol; j++) {
	long double tmp = a[rowLoc[rowOfLeadCol]*numCol + j] / denom;

	a[rowLoc[rowOfLeadCol]*numCol + j] = tmp;
      }
    }
    if(rowOfLeadCol != i) {
      int tmp;
      
      tmp = rowLoc[i];
      rowLoc[i] = rowLoc[rowOfLeadCol];
      rowLoc[rowOfLeadCol] = tmp;
    }
    /* step 3: Add a suitable value to each row below row i so that they have zero at column i */
    for(int j=i+1; j < numRow; j++) {
      long double factor = -a[rowLoc[j]*numCol + leadCol];

      for(int k=leadCol; k < numCol; k++)
	a[rowLoc[j]*numCol + k] += factor * a[rowLoc[i]*numCol + k];
    }
  }
}

/* Working upward to make each leading one the only nonzero number in
 * which column it be .
 * Parameters:
 * a: the matrix in a row echelon form.
 * rowLoc: a look-up table for rows' locations
 */
void specReduce(long double * a, int * rowLoc) {
  int leadCol;  // the column of the leading one in a row
  int i;

  i = (numRow > (numCol - 1))?(numCol-2):(numRow-1);
  for(; i>=0; i--) {
    //Find the leading 1, but if it's an all-zero row, skip it.
    leadCol = -1;
    for(int j=i; j<numCol; j++) {
      if(a[rowLoc[i]*numCol + j] != 0.0) {
	leadCol = j;
	break;
      }
    }
    // if it's not an all-zero row, reducing all other numbers in all
    // rows above at the column at where the leading 1 be.
    if(leadCol > -1) {
      for(int j=i-1; j >=0; j--) {
	long double factor = -a[rowLoc[j]*numCol + leadCol];

	for(int k=leadCol; k < numCol; k++) 
	  a[rowLoc[j]*numCol + k] += a[rowLoc[i]*numCol + k] * factor;
      }
    }
  }
}

/* Initializing parameters and assigning input values to the original
 * matrix.
 * Parameter:
 * argc: the first argument of main function
 * argv: the second argument of main function
 * a: the matrix owned by the process
 * loc: the Global Row Index -> Current Row Location table
 * idx: the Current Row Location  -> Global Row Index table
 */
void initialization(int argc, char * argv[], 
		    long double * a, int * loc, int * idx) {
#ifdef _CIVL
  long double spec[numRow*numCol];
  int rowLoc[numRow];

  for(int i=first; i<first+localRow; i++) 
    for(int j=0; j<numCol; j++) {
      a[(i-first)*numCol + j] = data[i][j];
    }
  //sequential run
  if(rank == 0) {
    for(int i=0; i<numRow; i++){
      rowLoc[i] = i;
      memcpy(&spec[i*numCol], &data[i][0], numCol * sizeof(long double));
    }
    specElimination(spec, rowLoc);
    specReduce(spec, rowLoc);
    for(int i=0; i<numRow; i++){
      for(int j=0; j<numCol; j++)
	oracle[i][j] = spec[rowLoc[i]*numCol + j];
    }
    printf("oracle is :\n");
    for(int i=0; i<numRow; i++)
    printRow(&oracle[i][0]);
  }
#else
  if((argc - 3) != numRow * numCol)
    printf("Too few arguments.\n"
           "Usage: mpiexec -n nprocs ./a.out n m A[0,0] A[0,1] ... A[n-1,m-1]\n"
           "   n : number of rows in matrix\n"
           "   m : number of columns in matrix\n"
           "   A[0,0] .. A[n-1,m-1] : entries of matrix (doubles)\n");
  first = firstForProc(rank);
  localRow = countForProc(rank);
  //initializing matrix
  for(int i=0; i<localRow; i++)
    for(int j=0; j<numCol; j++)
      sscanf(argv[(first+i)*numCol + j + 3], "%Lf", &a[i*numCol + j]);
#endif
  for(int i=0; i<numRow; i++){
    loc[i] = i;
    idx[i] = i;
  }
}

/* Set row to location loca */
void setLoc(int row, int loca){
  int tmpLoc, tmpIdx;

  tmpLoc = loc[row];
  tmpIdx = idx[loca];
  //swap locations(update index -> location table)
  loc[row] = loca;
  loc[tmpIdx] = tmpLoc;
  //update location -> index table
  idx[loca] = row;
  idx[tmpLoc] = tmpIdx;
}

/* Performs a gaussian elimination on the given matrix, the output
 * matrix will finally be in row echelon form .
 */
void gaussianElimination(long double *a) {
  /* Buffer for the current toppest unprocessed row. */
  long double top[numCol];

  /* For each row of the matrix, it will be processed once. */
  for(int i=0; i < numRow; i++) {
    /* owner of the current unprocessed top row */
    int owner = OWNER(idx[i]); 
    /* the column of the next leading 1, initial value is numCol 
     * because later it will pick up a minimum number.
     */
    int leadCol = numCol; 
    /* the global index of the row the next leading 1 will be in */
    int rowOfLeadCol = -1;
    int rowOfLeadColOwner;    // the owner of rowOfLeadCol
    /* message buffer: [0]:leadCol ;[1]:rowOfLeadCol */
    int sendbuf[2];
    /* receive buffer: it will contain lead 1 column candidates from
       all processes */
    int recvbuf[2*nprocs];   
    int tmp;

    //step 1: find out the local leftmost nonzero column
    for(int j=i; j < numCol; j++) {
      int k;

      for(k = first; k < first + localRow; k++) {
        // only look at unprocessed rows
        if(loc[k] >= i) {
          if(a[(k-first)*numCol+j] != 0.0) {
            leadCol = j;
            rowOfLeadCol = k; 
            break;
          }
        }
      }
      if(leadCol < numCol)
        break;
    }
    sendbuf[0] = leadCol;
    sendbuf[1] = rowOfLeadCol;
    /* All reduce the smallest column(left-most) of leading 1 to every
       process */
    MPI_Allreduce(sendbuf, recvbuf, 1, MPI_2INT, MPI_MINLOC, MPI_COMM_WORLD);
    leadCol = recvbuf[0];
    rowOfLeadCol = recvbuf[1];
    /* Now the row containing next leading 1 is decided, findout the
       owner of it. */
    rowOfLeadColOwner = OWNER(rowOfLeadCol);
    /* if leadCol is still initial value, it means there is no avaliable 
       column suitable for next leading 1. */
    if(leadCol == numCol)
     return;
    // step 2: reducing the leading number to 1
    if(rank == rowOfLeadColOwner) {
      long double denom = a[(rowOfLeadCol - first)*numCol + leadCol];

      if(denom != 0.0)
        for(int j=leadCol; j < numCol; j++)
          a[(rowOfLeadCol - first)*numCol + j] = a[(rowOfLeadCol - first)*numCol + j] / denom;
      memcpy(top, &a[(rowOfLeadCol - first)*numCol
                     ], numCol*sizeof(long double));
    }
    MPI_Bcast(top, numCol, MPI_LONG_DOUBLE, rowOfLeadColOwner, MPI_COMM_WORLD);
    /* swap the row containing next leading 1 to the top location of
       current submatrix */
    if(loc[rowOfLeadCol] != i)
      setLoc(rowOfLeadCol, i);
    /* step 3: add a suitable value to all unprocessed rows to make
       all numbers at the same column as leading 1 zeros. */
    for(int j=0; j < localRow; j++) {
      if(loc[j+first] > i){
        long double factor = -a[j*numCol + leadCol];

        for(int k=leadCol; k < numCol; k++) {
          a[j*numCol + k] += factor * top[k];
        }
      }
    }
  }
}

/* Perform a backward reduction on the given matrix which transforms a
   row echelon form to a reduced row echelon form */
void backwardReduce(long double *a) {
  int leadCol;
  int owner;
  int i;
  long double top[numCol];

  i = (numRow > (numCol - 1))?(numCol-2):numRow-1;
  for(; i>=1; i--) {
    leadCol = -1;
    owner = OWNER(idx[i]);
    if(rank == owner)
      memcpy(top, &a[(idx[i] - first)*numCol + i], (numCol-i)*sizeof(long double));
    MPI_Bcast(top, (numCol-i), MPI_LONG_DOUBLE, owner, MPI_COMM_WORLD);
    //find out the leading 1 column
    for(int j=0; j<(numCol-i); j++){
      if(top[j] != 0.0){
	leadCol = j+i;
	break;
      }
    }
    if(leadCol == -1)
      continue;
    else {
      for(int j=first; j<first+localRow; j++){
	if(loc[j] < i){
	  long double factor = -a[(j-first)*numCol + leadCol];

	  for(int k=leadCol; k<numCol; k++)
	    a[(j-first)*numCol + k] += factor*top[k-i];
	}
      }
    }
  }
}

int main(int argc, char *argv[]) {
  long double *a;

#ifndef _CIVL
  if(argc < 3) 
    printf("Expecting the arguments: numberOfRows  numberOfColumns\n");
  numRow = atoi(argv[1]);
  numCol = atoi(argv[2]);
  //#else
  //$elaborate(numRow);
  //$elaborate(numCol);
#endif
  MPI_Init(&argc, &argv);
  MPI_Comm_rank(MPI_COMM_WORLD, &rank);
  MPI_Comm_size(MPI_COMM_WORLD, &nprocs);
  first = firstForProc(rank);
  localRow = countForProc(rank);
  a = (long double*)malloc(numCol*localRow*sizeof(long double));
  loc = (int*)malloc(numRow*sizeof(int));
  idx = (int*)malloc(numRow*sizeof(int));
  initialization(argc, argv, a, loc, idx);
  gaussianElimination(a);
  backwardReduce(a);
  if(!rank)printf("After backward reduction, the matrix in reduced row echelon form is:\n");
  printSystem(a);
  MPI_Finalize();
  free(loc);
  free(idx);
  free(a);
  return 0;
}

