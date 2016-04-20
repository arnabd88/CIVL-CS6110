//
//  utils.c
//  cg
//
//  Created by Sri Hari Krishna Narayanan on 9/02/15.
//
//

#include <time.h>
#include <ctype.h>
#include <stdio.h>
#include <unistd.h>
#include <stdlib.h>
#include <math.h>
#include <assert.h>
#include "utils.h"
#include "mmio.h"


void matrixCopy (double **X, int n, int m, double **result){
  int i, j;
  for (i = 0 ; i < n; i++){
    for (j = 0 ; j < m; j++){
      result[i][j] =  X[i][j];
    }
  }
}

void matrixDifference (double **X, double **Y, int n, int m, double **result){
  int i, j;
  for (i = 0 ; i < n; i++)
    for (j = 0 ; j < m; j++)
      result[i][j] =  X[i][j] - Y[i][j];
}

void matrixMatrixProduct (double **X, double **Y, int n, int m, int ensemblecount, double **result){
  int i, j, k;
  double temp;
  for (i = 0 ; i < n; i++){
    for (j = 0 ; j < ensemblecount; j++) {
      temp = 0.0;
      for (k = 0 ; k < m; k++)
        temp +=  X[i][k] * Y[k][j];
      result[i][j] = temp;
    }
  }
}

void matrixVectorProduct (double **X, double *v, int n, int m, double *result){
  int i, j;
  double temp;
  for (i = 0 ; i < n; i++){
    temp = 0.0;
    for (j = 0 ; j < m; j++){
      temp +=  X[i][j] * v[j];
    }
    result[i] = temp;
  }
}

void vectorTransposeVectorProductInsideMatrix(double **X, double **Y, int n, int ensemblecount, double *result){
  int i, e;
  double temp;
  for (e = 0 ; e < ensemblecount; e++){
    temp = 0.0;
    for (i = 0 ; i < n; i++){
      temp +=  X[i][e] * Y[i][e];
    }
    result[e] = temp;
  }
}

void vectorVectorTransposeProductInsideMatrix(double **X, double **Y, int ensemblecount, int n, double *result){
  int i, e;
  double temp;
  for (e = 0 ; e < ensemblecount; e++){
    temp = 0.0;
    for (i = 0 ; i < n; i++){
      temp +=  X[e][i] * Y[e][i];
    }
    result[e] = temp;
  }
}


void vectorDifference (double *v1, double *v2, int n, double *result){
  int i;
  for (i = 0 ; i < n; i++){
    result[i] = v1[i] - v2[i];
  }
}

void vectorCopy (double *v1, int n, double *result){
  int i;
  for (i = 0 ; i < n; i++){
    result[i] = v1[i];
  }
}

double vectorTransposeVectorProduct (double *v1, double *v2, int n){
  int i;
  double result = 0.0;
  for (i = 0 ; i < n; i++){
    result += v1[i]*v2[i];
  }
  return result;
}

void diagonalPreconditioner( double **A, int n, int m){
  int  i,j;
  double val;
  for (i=0; i < n; i++) {
    val = 0.00001;
    if(A[i][i]!=0.0)
      val = 1.0 /sqrt(A[i][i]);
    for (j=0; j < n; j++)
      A[i][j] = val * A[i][j] *val;
  }
}

/* Euklidscher Norm von v ; Code from Kshitij Kulshreshtha
 */
void norm2PerColumn(double **const mat, size_t n, size_t ensemblecount, double *sum)
{
  size_t e, j;
  double abs,scale;
  for (e=0; e<ensemblecount; e++) {
    sum[e]=0.0;
    scale=0.0;
    for (j=0; j<n; j++) {
      if (mat[j][e] != 0.0) {
        abs = fabs(mat[j][e]);
        if (scale <= abs) {
          sum[e] = 1.0 + sum[e] * (scale/abs)*(scale/abs);
          scale = abs;
        } else
          sum[e] += (abs/scale)*(abs/scale);
      }
    }
    sum[e] = sqrt(sum[e])*scale;
  }
}

/* Euklidscher Norm von v ; Code from Kshitij Kulshreshtha
 */
void norm2PerRow(double **const mat, size_t ensemblecount, size_t n, double *sum)
{
  size_t e, j;
  double abs,scale;
  for (e=0; e<ensemblecount; e++) {
    sum[e]=0.0;
    scale=0.0;
    for (j=0; j<n; j++) {
      if (mat[e][j] != 0.0) {
        abs = fabs(mat[e][j]);
        if (scale <= abs) {
          sum[e] = 1.0 + sum[e] * (scale/abs)*(scale/abs);
          scale = abs;
        } else
          sum[e] += (abs/scale)*(abs/scale);
      }
    }
    sum[e] = sqrt(sum[e])*scale;
  }
}

int haveConvergedPerRow(double **matrix1, double *vector1, int ensemblecount, int n, int policy, double tolerance, int iteration, int *converged){
  double testval;
  double *testvalvec1 = (double *) malloc (ensemblecount *sizeof(double));
  double testvalvec2;
  int convergedcount = 0, e;
  norm2PerRow(matrix1, ensemblecount, n, testvalvec1);
  testvalvec2 = norm2(vector1, n);
  convergedcount = 0;
  for(e =0; e<ensemblecount; e++) {
    testval = testvalvec1[e]/testvalvec2;
    if(testval <= tolerance){
      if(converged[e]<0)
        converged[e] = iteration;
      convergedcount++;
    }
    //printf("  testvalvec1[e] %lg testvalvec2[e] %lg testval %lg", testvalvec1[e], testvalvec2, testval);
  }
  //printf("  convergedcount %d,  ensemblecount %d \n", convergedcount, ensemblecount);
  free(testvalvec1);
  if (policy ==0)
    return convergedcount==ensemblecount;
  else if(policy ==1)
    return convergedcount>=1;
  return (convergedcount>= (ensemblecount/2));
}

int haveConvergedPerColumn(double **matrix1, double **matrix2, int n, int ensemblecount, int policy, double tolerance, int iteration, int *converged){
  double testval;
  double *testvalvec1 = (double *) malloc (ensemblecount *sizeof(double));
  double *testvalvec2 = (double *) malloc (ensemblecount *sizeof(double));
  int convergedcount = 0, e;
  norm2PerColumn(matrix1, n, ensemblecount, testvalvec1);
  norm2PerColumn(matrix2, n, ensemblecount, testvalvec2);
  convergedcount = 0;
  for(e =0; e<ensemblecount; e++) {
    testval = testvalvec1[e]/testvalvec2[e];
    if(testval <= tolerance){
      if(converged[e]<0)
        converged[e] = iteration;
      convergedcount++;
    }
    //printf("  testvalvec1[e] %lg testvalvec2[e] %lg testval %lg", testvalvec1[e], testvalvec2[e], testval);
  }
  //printf("  convergedcount %d,  ensemblecount %d \n", convergedcount, ensemblecount);
  free(testvalvec1);
  free(testvalvec2);
  if (policy ==0)
    return convergedcount==ensemblecount;
  else if(policy ==1)
    return convergedcount>=1;
  return (convergedcount>= (ensemblecount/2));
}


/* Euklidscher Norm von v ; Code from Kshitij Kulshreshtha
 */
double norm2(const double *const v, const size_t n)
{
  size_t j;
  double abs,scale,sum;
  scale=0.0;
  sum=0.0;
  for (j=0; j<n; j++) {
    if (v[j] != 0.0) {
      abs = fabs(v[j]);
      if (scale <= abs) {
        sum = 1.0 + sum * (scale/abs)*(scale/abs);
        scale = abs;
      } else
        sum += (abs/scale)*(abs/scale);
    }
  }
  sum = sqrt(sum)*scale;
  return sum;
}


// SHK: Function to return posive and negative random numbers
// Returns in the half-open interval [-max/2, max/2]
// Original copied from:
// http://stackoverflow.com/questions/2509679/how-to-generate-a-random-number-from-within-a-range
// Adapted to return -ve numbers as well
// Assumes 0 <= max <= RAND_MAX
// Returns in the half-open interval [0, max]
long random_at_most(long max) {
  unsigned long
  // max <= RAND_MAX < ULONG_MAX, so this is okay.
  num_bins = (unsigned long) max + 1,
  num_rand = (unsigned long) RAND_MAX + 1,
  bin_size = num_rand / num_bins,
  defect   = num_rand % num_bins;
  
  long x;
  do {
    x = random();
  }
  // This is carefully written not to overflow
  while (num_rand - defect <= (unsigned long)x);
  
  // Truncated division is intentional
  return x/bin_size - (max/2);
}


double ** createMatrix( int n, int m){
  int i,j;
  double ** A = (double **) malloc (n*sizeof(double *));
  for(i = 0; i < n ; i++) {
    A[i] = (double *) malloc (m *sizeof(double));
    for(j = 0; j < m ; j++)
      A[i][j] = 0.0;
  }
  return A;
}

void destroyMatrix( double **A, int n){
  int i;
  for(i = 0; i < n ; i++)
    free(A[i]);
  free(A);
}

int createDirectionVector(int M, const char * directionfilename, double **direction){
  int j, ret=0, directionM, tempensemblecount;
  if(directionfilename!=NULL) {
    ret = mm_read_rhs(directionfilename, &directionM, &tempensemblecount, direction);
    if(ret !=0) {
      fprintf (stderr, "\n Error in reading file %s.\n", directionfilename);
      return -1;
    }
    if(tempensemblecount!=1) {
      fprintf (stderr, "\n Direction vector file should have only 1 vector. Instead have %d vectors.\n", tempensemblecount);
      return -1;
    }
    if(M!=directionM) {
      fprintf (stderr, "\n Length of RHS vector is %d, Length of direction Vector is %d. They should be the same\n", M, directionM);
      return -1;
    }
  } else {
    *direction = (double *) malloc (M*sizeof(double));
    //    srand(time(NULL));
    srand(179); // For reproducibility
    for(j = 0; j < M ; j++)
      (*direction)[j] = (double) random_at_most(M)/(M/2);
  }
  return 0;
}

int createRHSMatrix(double ***b, int *M, int *ensemblecount, const char * rhsfilename, const char * directionfilename, double scalingfactor) {
  int *I, *J, ret, i, j;
  double *val, *direction;
  int rhsvectorcount;
  if(rhsfilename!=NULL){
    ret = mm_read_rhs(rhsfilename, M, &rhsvectorcount, &val);
    if(ret !=0) {
      fprintf (stderr, "\n Error in reading file %s.\n", rhsfilename);
      return -1;
    }
    if(rhsvectorcount!=1) {
      fprintf (stderr, "\n RHS should have only 1 vector. Instead have %d vectors.\n", rhsvectorcount);
      return -1;
    }
    ret = createDirectionVector(*M, directionfilename, &direction);
    if(ret!=0){
      printf("\n Error Forming direction vector \n");
      return -1;
    }
    assert(ensemblecount!=NULL);
    *b = createMatrix(*ensemblecount, *M);
    for(i = 0; i < *ensemblecount; i++)
      for(j = 0; j < *M ; j++)
        (*b)[i][j] = val[j]+ i*scalingfactor*direction[j];
    free(val);
    free(direction);
  } else {
    assert(M!=NULL);
    assert(ensemblecount!=NULL);
    *b = createMatrix(*ensemblecount, *M);
  }
  return 0;
}

int createRHSMatrixTranspose(double ***b, int *M, int *ensemblecount, const char * rhsfilename, const char * directionfilename, double scalingfactor) {
  int *I, *J, ret=0, i, j;
  double *val;
  double *direction;
  int rhsvectorcount;
  if(rhsfilename!=NULL) {
    ret = mm_read_rhs(rhsfilename, M, &rhsvectorcount, &val);
    if(ret !=0) {
      fprintf (stderr, "\n Error in reading file %s.\n", rhsfilename);
      return -1;
    }
    if(rhsvectorcount!=1) {
      fprintf (stderr, "\n RHS should have only 1 vector. Instead have %d vectors.\n", rhsvectorcount);
      return -1;
    }
    createDirectionVector(*M, directionfilename, &direction);
    assert(ensemblecount!=NULL);
    *b = createMatrix(*M,*ensemblecount);
    for(i = 0; i < *ensemblecount; i++)
      for(j = 0; j < *M ; j++)
        (*b)[j][i] = val[j]+ i*scalingfactor*direction[j];
    free(val);
    free(direction);
  } else {
    assert(M!=NULL);
    assert(ensemblecount!=NULL);
    *b = createMatrix(*M,*ensemblecount);
  }
  return 0;
}

int readMatrixFile(const char * filename, int *M, int *N, int *NZ, double**val, int **I, int **J){
  int ret = mm_read_symmetric_sparse(filename, M, N, NZ, val, I, J);
  if(ret !=0) {
    fprintf (stderr, "\n Error in reading file %s.\n", filename);
    return -1;
  }
  if(*M!=*N){
    fprintf (stderr, "\n Expected a square matrix.\n");
    return -1;
  }
  return 0;
}

int createMatrixEmsemble(double **A, int M, int ensemblecount, const char * directionfilename, double scalingfactor, double ****Aensemble) {
  int *I, *J, ret, i, j;
  double *val, *direction;
  int rhsvectorcount;
  createDirectionVector(M, directionfilename, &direction);
  assert(ensemblecount>0);
  *Aensemble = (double ***) malloc(ensemblecount *sizeof(double**));
  for(i = 0; i < ensemblecount; i++) {
    (*Aensemble)[i] = createMatrix(M, M);
    matrixCopy(A, M, M, (*Aensemble)[i]);
    for(j = 0; j < M ; j++)
      (*Aensemble)[i][j][j] = (*Aensemble)[i][j][j] + i*scalingfactor*direction[j];
    
  }
  free(direction);
  return 0;
}

//Sparse Routines
int createMatrixEmsembleCSR(int NZ, int *row, int *col_idx, double *val, int M, int ensemblecount, const char * directionfilename, double scalingfactor, double ***valensemble) {
    int *I, *J, ret, i, j;
    double *direction;
    int rhsvectorcount;
    createDirectionVector(M, directionfilename, &direction);
    assert(ensemblecount>0);
    *valensemble = (double **) malloc(ensemblecount *sizeof(double*));
    for(i = 0; i < ensemblecount; i++) {
        (*valensemble)[i] = malloc(NZ*sizeof(double));
        int currrowindex=0, currvalindex=0;
        for (currrowindex = 0; currrowindex < M; currrowindex++) {
            //now look ahead and search for the diagonal element
            int found = 0;
            currvalindex = row[currrowindex];
            for(j=0;j<row[currrowindex+1]-row[currrowindex]; j++) {
                (*valensemble)[i][currvalindex+j] = val[currvalindex+j];
                if(currrowindex==col_idx[currvalindex+j]){
                    (*valensemble)[i][currvalindex+j] += i*scalingfactor*direction[col_idx[currvalindex+j]];
                    found++;
                }
            }
            if(found==0){
                printf("\ndiagonalDirectionIncrementCSR: Unhandled case of an empty diagonal element at row %d", currrowindex);
                exit(0);
            }
            if(found>1){
                printf("\ndiagonalDirectionIncrementCSR: Unhandled case of an multiple diagonal elements at row %d", currrowindex);
                exit(0);
            }
        }
    }
    free(direction);
    return 0;
}

void diagonalDirectionIncrementCSR(int numrows, int *row, int*col, double* val, int e, double scalingfactor, double *direction){
  int  i,j;
  double diagval;
  int currrowindex=0, currvalindex=0;
  for (currrowindex = 0; currrowindex < numrows; currrowindex++) {
    diagval = e*scalingfactor*direction[currrowindex];
    //now look ahead and search for the diagonal element
    int found = 0;
    currvalindex = row[currrowindex];
    for(i=0;i<row[currrowindex+1]-row[currrowindex]; i++) {
      if(currrowindex==col[currvalindex+i]){
        val[currvalindex+i]+= diagval;
        found++;
      }
    }
    if(found==0){
      printf("\ndiagonalDirectionIncrementCSR: Unhandled case of an empty diagonal element at row %d", currrowindex);
      exit(0);
    }
    if(found>1){
      printf("\ndiagonalDirectionIncrementCSR: Unhandled case of an multiple diagonal elements at row %d", currrowindex);
      exit(0);
    }
  }
}

void diagonalPreconditionerCSR(int numrows, int *row, int*col, double* val){
  int  i,j;
  double diagval;
  int currrowindex=0, currvalindex=0;
  for (currrowindex = 0; currrowindex < numrows; currrowindex++) {
    diagval = 0.00001;
    //now look ahead and search for the diagonal element
    int found = 0;
    for(i=0;i<row[currrowindex+1]-row[currrowindex]; i++) {
      if(currrowindex==col[currvalindex+i]){
        val[currvalindex+i]+=1.0;
        diagval = 1 / sqrt(val[currvalindex+i]);
        found++;
      }
    }
    if(found==0){
      printf("\ndiagonalPreconditionerCSR: Unhandled case of an empty diagonal element at row %d", currrowindex);
      exit(0);
    }
    if(found>1){
      printf("\ndiagonalPreconditionerCSR: Unhandled case of an multiple diagonal elements at row %d", currrowindex);
      exit(0);
    }
    //now adjust the values of the row
    for(i=0;i<row[currrowindex+1]-row[currrowindex]; i++) {
      val[currvalindex] = diagval * val[currvalindex] * diagval;
      currvalindex++;
    }
  }
}

void matrixVectorProductCSR (int NZ, int *row, int *col_idx, double *val, double *v, int n, double *result){
  int i, currvalindex=0, currrowindex;
  double temp;
  for (currrowindex = 0; currrowindex < n; currrowindex++) {
    temp = 0.0;
    currvalindex = row[currrowindex];
    for(i=0;i<row[currrowindex+1]-row[currrowindex]; i++){
      temp +=  val[currvalindex + i] * v[col_idx[currvalindex + i]];
    }
    result[currrowindex] = temp;
  }
}

void getDiagonalFromCSR (int n, int *row, int *col, double *val, double *result){
  int i, currvalindex=0, currrowindex;
  for (currrowindex = 0; currrowindex < n; currrowindex++) {
    int found = 0;
    currvalindex = row[currrowindex];
    for(i=0;i<row[currrowindex+1]-row[currrowindex]; i++) {
      if(currrowindex==col[currvalindex+i]){
        result[currrowindex] = val[currvalindex+i];
        found++;
      }
    }
    if(found==0){
      printf("\n getDiagonalFromCSR: Unhandled case of an empty diagonal element at row %d", currrowindex);
      exit(0);
    }
    if(found>1){
      printf("\n getDiagonalFromCSR: Unhandled case of an multiple diagonal elements at row %d currvalindex %d", currrowindex, currvalindex);
      exit(0);
    }
  }
}

void formRHSCSR(int NZ, int *row, int *col, double *val, int M, int N, int ensemblecount, int wantindependentensemble ,double **b){
  double * btemp, **xref, *xtemp;
  int i,j;
  btemp = (double *) malloc (N *sizeof(double));
  xref = createMatrix(M, ensemblecount);
  xtemp = (double *) malloc (N *sizeof(double));
  srand(time(NULL));
  if(wantindependentensemble==0){
    for(i = 0; i < N ; i++)
      xref[i][0] = (double) random_at_most(N)/(N/2);
    
    for(j = 0; j < N ; j++)
      for(i = 1; i < ensemblecount; i++)
        xref[j][i] = xref[j][0] * (i+1);
    
    for(i = 0; i < ensemblecount; i++) {
      for(j = 0; j < N ; j++)
        xtemp[j] = xref[j][i];
      matrixVectorProductCSR(NZ, row, col, val, xtemp, M, b[i]);
    }
  } else {
    for(i = 0; i < ensemblecount; i++) {
      for(j = 0; j < N ; j++)
        xtemp[j] = (double) random_at_most(N)/(N/2);
      matrixVectorProductCSR(NZ, row, col, val, xtemp, M, b[i]);
    }
  }
  
  free(xtemp);
  free(btemp);
  destroyMatrix(xref, M);
}

void formRHSTransposeCSR(int NZ, int *row, int *col, double *val, int M, int N, int ensemblecount, int wantindependentensemble ,double **b){
    double * btemp, **xref, *xtemp;
    int i,j;
    btemp = (double *) malloc (N *sizeof(double));
    xref = createMatrix(M, ensemblecount);
    xtemp = (double *) malloc (N *sizeof(double));
    srand(time(NULL));
    if(wantindependentensemble==0){
        for(i = 0; i < N ; i++)
            xref[i][0] = (double) random_at_most(N)/(N/2);
        
        for(j = 0; j < N ; j++)
            for(i = 1; i < ensemblecount; i++)
                xref[j][i] = xref[j][0] * (i+1);
        
        for(i = 0; i < ensemblecount; i++) {
            for(j = 0; j < N ; j++)
                xtemp[j] = xref[j][i];
            matrixVectorProductCSR(NZ, row, col, val, xtemp, M, btemp);
            for(j = 0; j < N ; j++)
                b[j][i] = btemp[j];
        }
    } else {
        for(i = 0; i < ensemblecount; i++) {
            for(j = 0; j < N ; j++)
                xtemp[j] = (double) random_at_most(N)/(N/2);
            matrixVectorProductCSR(NZ, row, col, val, xtemp, M, btemp);
            for(j = 0; j < N ; j++)
                b[j][i] = btemp[j];
        }
    }
    
    free(xtemp);
    free(btemp);
    destroyMatrix(xref, M);
}

void matrixMatrixProductCSR (int NZ, int *row, int *col_idx, double *val, double **Y, int n, int m, int ensemblecount, double **result){
    int i, e, currvalindex=0, currrowindex;
    double temp;
    for (currrowindex = 0; currrowindex < n; currrowindex++) {
        for (e = 0 ; e < ensemblecount; e++) {
          temp = 0.0;
          currvalindex = row[currrowindex];
          for(i=0;i<row[currrowindex+1]-row[currrowindex]; i++){
            temp +=  val[currvalindex + i] * Y[col_idx[currvalindex + i]][e];
          }
          result[currrowindex][e] = temp;
        }
    }
}

void formRHS(double** A, int M, int N, int ensemblecount, int wantindependentensemble ,double **b){
  double * btemp, **xref, *xtemp;
  int i,j;
  btemp = (double *) malloc (N *sizeof(double));
  xref = createMatrix(M, ensemblecount);
  xtemp = (double *) malloc (N *sizeof(double));
  srand(time(NULL));
  if(wantindependentensemble==0){
    for(i = 0; i < N ; i++)
      xref[i][0] = (double) random_at_most(N)/(N/2);
    
    for(j = 0; j < N ; j++)
      for(i = 1; i < ensemblecount; i++)
        xref[j][i] = xref[j][0] * (i+1);
    
    for(i = 0; i < ensemblecount; i++) {
      for(j = 0; j < N ; j++)
        xtemp[j] = xref[j][i];
      matrixVectorProduct(A, xtemp, M, N, b[i]);
    }
  } else {
    for(i = 0; i < ensemblecount; i++) {
      for(j = 0; j < N ; j++)
        xtemp[j] = (double) random_at_most(N)/(N/2);
      matrixVectorProduct(A, xtemp, M, N, b[i]);
    }
  }
  
  free(xtemp);
  free(btemp);
  destroyMatrix(xref, M);
}

void formRHSTranspose(double** A, int M, int N, int ensemblecount, int wantindependentensemble ,double **b){
  double * btemp, **xref, *xtemp;
  int i,j;
  btemp = (double *) malloc (N *sizeof(double));
  xref = createMatrix(M, ensemblecount);
  xtemp = (double *) malloc (N *sizeof(double));
  srand(time(NULL));
  if(wantindependentensemble==0){
    for(i = 0; i < N ; i++)
      xref[i][0] = (double) random_at_most(N)/(N/2);
    
    for(j = 0; j < N ; j++)
      for(i = 1; i < ensemblecount; i++)
        xref[j][i] = xref[j][0] * (i+1);
    
    for(i = 0; i < ensemblecount; i++) {
      for(j = 0; j < N ; j++)
        xtemp[j] = xref[j][i];
      matrixVectorProduct(A, xtemp, M, N, btemp);
      for(j = 0; j < N ; j++)
        b[j][i] = btemp[j];
    }
  } else {
    for(i = 0; i < ensemblecount; i++) {
      for(j = 0; j < N ; j++)
        xtemp[j] = (double) random_at_most(N)/(N/2);
      matrixVectorProduct(A, xtemp, M, N, btemp);
      for(j = 0; j < N ; j++)
        b[j][i] = btemp[j];
    }
  }
  
  free(xtemp);
  free(btemp);
  destroyMatrix(xref, M);
}

void output(int *converged, double * normval, int ensemblecount){
  int i;
  for(i = 0; i < ensemblecount ; i++){
    if(converged[i]>=0){
      printf ("\tnorm2(x[%d]^2):       %lg, converged in %d \n", i, normval[i]*normval[i], converged[i]);
      FILE* fh=fopen("norm.out","a+");
      fprintf (fh,"%.16e %d\n",normval[i]*normval[i], converged[i]);
      fclose(fh);
    } else
      printf ("\tnorm2(x[%d]^2):       NC\n", i);
  }
}

