//
//  utils.h
//  cg
//
//  Created by Sri Hari Krishna Narayanan on 9/02/15.
//
//

#ifndef __cg__utils__
#define __cg__utils__
/** @brief slow matrix copy. Should be reduced to a memcpy()
 *  @param X src matrix.
 *  @param n #rows.
 *  @param m #columns.
 *  @param result output matrix.
 *  @return Void.
 */
void matrixCopy (double **X, int n, int m, double **result);

/** @brief result_{ij} = X_{ij} -Y_{ij}
 *  @param X src matrix.
 *  @param Y src matrix.
 *  @param n #rows.
 *  @param m #columns.
 *  @param result output matrix.
 *  @return Void.
 */
void matrixDifference (double **X, double **Y, int n, int m, double **result);

/** @brief matrix matrix multiply.
 *  @param X src matrix (n*m).
 *  @param Y src matrix. (m*ensemblecount)
 *  @param n #rows in X.
 *  @param m #columns in X and rows in Y.
 *  @param ensemblecount #columns in Y.
 *  @param result output matrix.
 *  @return Void.
 */
void matrixMatrixProduct (double **X, double **Y, int n, int m, int ensemblecount, double **result);

/** @brief computes matrix times vector result_i = \sigma_j{x_{ij}*v_j}.
 *  @param X src matrix (n*m).
 *  @param v src vector. (m)
 *  @param n #rows in X.
 *  @param m #columns in X.
 *  @param result output vector.
 *  @return Void.
 */
void matrixVectorProduct (double **X, double *v, int n, int m, double *result);

/** @brief result_e = \sigma_j{X_{ie}*Y_{ie}}.
 *  @param X src matrix (n*ensemblecount).
 *  @param Y src matrix. (n*ensemblecount)
 *  @param n #rows in X and Y.
 *  @param ensemblecount #columns in X and Y.
 *  @param result output vector.
 *  @return Void.
 */
void vectorTransposeVectorProductInsideMatrix(double **X, double **Y, int n, int ensemblecount, double *result);

/** @brief result_e = \sigma_j{X_{ei}*Y_{ei}}.
 *  @param X src matrix (ensemblecount*n).
 *  @param Y src matrix. (ensemblecount*n)
 *  @param ensemblecount #rows in X and Y.
 *  @param n #columns in X and Y.
 *  @param result output vector.
 *  @return Void.
 */
void vectorVectorTransposeProductInsideMatrix(double **X, double **Y, int ensemblecount, int n, double *result);

/** @brief result_i = v1_i-v2_i.
 *  @param v1 src vector (n).
 *  @param v2 src vector. (n)
 *  @param n length of v1 and v2.
 *  @param result output vector.
 *  @return Void.
 */
void vectorDifference (double *v1, double *v2, int n, double *result);

/** @brief result_i = v1_i.
 *  @param v1 src vector (n).
 *  @param n length of v1.
 *  @param result output vector.
 *  @return Void.
 */
void vectorCopy (double *v1, int n, double *result);

/** @brief result = \sigma_i{v1_i*v2_i}.
 *  @param v1 src vector (n).
 *  @param v2 src vector. (n)
 *  @param n length of v1 and v2.
 *  @param result output scalar.
 *  @return scalar variable result.
 */
double vectorTransposeVectorProduct (double *v1, double *v2, int n);

/** @brief In place diagonal preconditioner of matrix A.
 *  @param A src and output matrix (n*m).
 *  @param n #rows.
 *  @param m #columns.
 *  @return Void.
 */
void diagonalPreconditioner( double **A, int n, int m);

/** @brief Computes the Euclidean norm for each row in the matrix.
 *  @param mat src matrix (emsemblecount*n).
 *  @param emsemblecount #rows.
 *  @param n #columns.
 *  @param sum output vector of norms.
 *  @return Void.
 */
void norm2PerRow(double **const mat, size_t ensemblecount, size_t n, double *sum);

/** @brief Computes the Euclidean norm for each column in the matrix.
 *  @param mat src matrix (n*emsemblecount).
 *  @param n #rows.
 *  @param emsemblecount #columns.
 *  @param sum output vector of norms.
 *  @return Void.
 */
void norm2PerColumn(double **const mat, size_t n, size_t ensemblecount, double *sum);

/** @brief If the Euclidean norm of a row in the matrix1 divided by the norm of vector1 is less than tolerance, the ensemble corresponding to that row has converged. Based on the convergence policyt, the total number of converged ensembles is used to decide if overall convergence has been reached.
 *  @param matrix1 src matrix (emsemblecount*n).
 *  @param vector1 src vector (emsemblecount*n).
 *  @param emsemblecount #rows of matrix1.
 *  @param n #columns of matrix1 and length of vector1.
 *  @param policy (allconverge=0, anyconverge=1, halfconverge=2).
 *  @param tolerance value that decides whether an ensemble has conerged.
 *  @param iteration current iteration.
 *  @param converged integer vector (length e) containing the iteration at which the ensemble converged.
 *  @return tolerance.
 */
int haveConvergedPerRow(double **matrix1, double *vector1, int ensemblecount, int n, int policy, double tolerance, int iteration, int *converged);

/** @brief If the quotient of the Euclidean norm of a column in the matrix1 divided by the norm of corresponging column in matrix2 vector2 is less than tolerance, the ensemble corresponding to that column in matrix1 has converged. Based on the convergence policy, the total number of converged ensembles is used to decide if overall convergence has been reached.
 *  @param matrix1 src matrix (n*emsemblecount).
 *  @param matrix2 src metrix (n*emsemblecount).
 *  @param n #rows of matrix1 and matrix2.
 *  @param emsemblecount #cols of matrix1 and matrix2.
 *  @param policy (allconverge=0, anyconverge=1, halfconverge=2).
 *  @param tolerance value that decides whether an ensemble has conerged.
 *  @param iteration current iteration.
 *  @param converged integer vector (length e) containing the iteration at which the ensemble converged.
 *  @return tolerance.
 */
int haveConvergedPerColumn(double **matrix1, double **matrix2, int n, int ensemblecount, int policy, double tolerance, int iteration, int *converged);

/** @brief Computes the Euclidean norm of a vector.
 *  @param v src vector .
 *  @param n length of v.
 *  @return Euclidean norm of v.
 */
double norm2(const double *const v, const size_t n);

/** @brief Function to return postive and negative random numbers in the half-open interval [-max/2, max/2]
 *
 * Original copied from:
 * http://stackoverflow.com/questions/2509679/how-to-generate-a-random-number-from-within-a-range
 * Adapted to return -ve numbers as well
 * Assumes 0 <= max <= RAND_MAX
 * @return a random number in the half-open interval [0, max]
 */
long random_at_most(long max);

/** @brief naively create an n*m matrix and initialize its entries to 0.0
 *  @param n #rows.
 *  @param m #columns.
 *  @return matrix
 */
double ** createMatrix( int n, int m);

/** @brief deallocate matrix
 *  @param A src matrix (n rows).
 *  @param n #rows.
 *  @return Void
 */
void destroyMatrix( double **A, int n);

/** @brief if directionfilename is not NULL, read a direction vector from a file, else create it
 *  @param M #rows that the direction vector should have.
 *  @param directionfilename file containing an input direction vector (can be NULL).
 *  @param direction output direction vector.
 *  @return 0 on success -1 on failure
 */
int createDirectionVector(int M, const char * directionfilename, double **direction);

/** @brief if rhsfilename is not NULL, read a basis RHS vector from a file, create a direction vector and create a matrix ((b_{ij} = vector_j+ i*scalingfactor*direction_j). Otherwise create an (ensemblecount*M) matrix with all entries 0.0.
 *  @param b output RHS matrix.
 *  @param M #cols in RHS matrix.
 *  @param ensemblecount #rows in RHS matrix.
 *  @param rhsfilename file containing a single RHS vector can be NULL).
 *  @param directionfilename file containing an input direction vector (can be NULL).
 *  @param scalingfactor value used to scale entries of the RHS matrix.
 *  @return 0 on success -1 on failure
 */
int createRHSMatrix(double ***b, int *M, int *ensemblecount, const char * rhsfilename, const char * directionfilename, double scalingfactor);

/** @brief if rhsfilename is not NULL, read a basis RHS vector from a file, create a direction vector and create a matrix ((b_{ji} = vector_j+ i*scalingfactor*direction_j). Otherwise create an (M*ensemblecount) matrix with all entries 0.0.
 *  @param b output RHS matrix.
 *  @param M #rows in RHS matrix.
 *  @param ensemblecount #cols in RHS matrix.
 *  @param rhsfilename file containing a single RHS vector can be NULL).
 *  @param directionfilename file containing an input direction vector (can be NULL).
 *  @param scalingfactor value used to scale entries of the RHS matrix.
 *  @return 0 on success -1 on failure
 */
int createRHSMatrixTranspose(double ***b, int *M, int *ensemblecount, const char * rhsfilename, const char * directionfilename, double scalingfactor);

/** @brief interface to mm_read_symmetric_sparse() which reads a sparse matrix from a file.
 *  @param filename file containing a matrix in matrix market format).
 *  @param M output #rows in the matrix.
 *  @param N output #cols in the matrix.
 *  @param NZ output #nonzeroes in the matrix.
 *  @param val output values the matrix.
 *  @param I output row coordinates of entries of val.
 *  @param J output col coordinates of entires of val.
 *  @return 0 on success -1 on failure
 */
int readMatrixFile(const char * filename, int *M, int *N, int *NZ, double**val, int **I, int **J);

/** @brief Copy matrix A to create a matrix ensemble. Then scale the diagonal entries of each matrix Aensemble_{ijj} += i*scalingfactor*direction[j];
 *  @param A src matrix (M*M).
 *  @param M #rows and #cols in A.
 *  @param ensemblecount #entires in the ensemble.
 *  @param directionfilename file containing an input direction vector (can be NULL).
 *  @param scalingfactor value used to scale entries of the RHS matrix.
 *  @param Aensemble output ensemble.
 *  @return 0 on success -1 on failure
 */
int createMatrixEmsemble(double **A, int M, int ensemblecount, const char * directionfilename, double scalingfactor, double ****Aensemble);

/** @brief Copy CSR matrix to create a matrix ensemble. Then scale the diagonal entries of each CSR matrix The dense version of this will be: Aensemble_{ijj} += i*scalingfactor*direction[j];
 *  @param NZ #nonzeroes in the CSR matrix.
 *  @param row rows of the CSR matrix.
 *  @param col_idx cols of the CSR matrix.
 *  @param val values of CSR matrix (size: NZ).
 *  @param ensemblecount #entires in the ensemble.
 *  @param directionfilename file containing an input direction vector (can be NULL).
 *  @param scalingfactor value used to scale entries of the RHS matrix.
 *  @param valensemble output ensemble(enmblecount *NZ).
 *  @return 0 on success -1 on failure
 */
int createMatrixEmsembleCSR(int NZ, int *row, int *col_idx, double *val, int M, int ensemblecount, const char * directionfilename, double scalingfactor, double ***valensemble);

/** @brief Scale the diagonal elements of a CSR matrix inplace. The dense version of this will be: Aensemble_{ii} += e*scalingfactor*direction[i];
 *  @param numrows #rows of the CSR matrix.
 *  @param row rows of the CSR matrix.
 *  @param col cols of the CSR matrix.
 *  @param val values of CSR matrix (size: NZ).
 *  @param scalingfactor value used to scale entries of the RHS matrix.
 *  @param direction direction vector used in scaling (size: numrows).
 *  @return Void
 */
void diagonalDirectionIncrementCSR(int numrows, int *row, int*col, double* val, int e, double scalingfactor, double *direction);

/** @brief In place diagonal preconditioner of CSR matrix.
 *  @param I row coordinates of entries of val.
 *  @param J col coordinates of entires of val.
 *  @param val input and output values the matrix.
 *  @return Void.
 */
void diagonalPreconditionerCSR(int nz, int *I, int*J, double* val);

/** @brief Matrix vector product of CSR matrix and vector.
 *  @param NZ #nonzeroes in the CSR matrix.
 *  @param row rows of the CSR matrix.
 *  @param col_idx cols of the CSR matrix.
 *  @param val values the matrix.
 *  @param v src vector of lenght n
 *  @param n #rows in v and matrix.
 *  @param result output vector.
 *  @return Void.
 */
void matrixVectorProductCSR (int NZ, int *row, int *col_idx, double *val, double *v, int n, double *result);

/** @brief Extract the diagonal elments of the CSR matrix.
 *  @param n #rows in matrix.
 *  @param row rows of the CSR matrix.
 *  @param col cols of the CSR matrix.
 *  @param val values the matrix.
 *  @param result output vector of length n.
 *  @return Void.
 */
void getDiagonalFromCSR (int n, int *row, int *col, double *val, double *result);

/** @brief Use a CSR matrix and a random x to create an ensemble of RHS vector that is ensemblecount in size.
 *  @param NZ #nonzeroes in the CSR matrix.
 *  @param row rows of the CSR matrix.
 *  @param col cols of the CSR matrix.
 *  @param val values the matrix.
 *  @param M #rows in the matrix.
 *  @param N #cols in the matrix.
 *  @param ensemblecount #entires in the ensemble.
 *  @param wantindependentensemble <0|1>. If true, create a new x vector for each ensemble.
 *  @param b output RHS ensemble (ensemblecount*M).
 *  @return Void.
 */
void formRHSCSR(int NZ, int *row, int *col, double *val, int M, int N, int ensemblecount, int wantindependentensemble ,double **b);

/** @brief Use a CSR matrix and a random x to create an ensemble of RHS vector that is ensemblecount in size.
 *  @param NZ #nonzeroes in the CSR matrix.
 *  @param row rows of the CSR matrix.
 *  @param col cols of the CSR matrix.
 *  @param val values the matrix.
 *  @param M #rows in the matrix.
 *  @param N #cols in the matrix.
 *  @param ensemblecount #entires in the ensemble.
 *  @param wantindependentensemble <0|1>. If true, create a new x vector for each ensemble.
 *  @param b output RHS ensemble (M*ensemblecount).
 *  @return Void.
 */
void formRHSTransposeCSR(int NZ, int *row, int *col, double *val, int M, int N, int ensemblecount, int wantindependentensemble ,double **b);

/** @brief Matrix matrix product of two CSR matrices.
 *  @param NZ #nonzeroes in the CSR matrix.
 *  @param row rows of the CSR matrix.
 *  @param col_idx cols of the CSR matrix.
 *  @param val values the CSR matrix1.
 *  @param Y values the CSR matrix2.
 *  @param result output vector of length n.
 *  @return Void.
 */
void matrixMatrixProductCSR (int NZ, int *row, int *col_idx, double *val, double **Y, int n, int m, int ensemblecount, double **result);

/** @brief Use A and a random x to create an ensemble of RHS vector that is ensemblecount in size.
 *  @param A src matrix (M*N) CSR matrix.
 *  @param M #rows in the matrix.
 *  @param N #cols in the matrix.
 *  @param ensemblecount #entires in the ensemble.
 *  @param wantindependentensemble <0|1>. If true, create a new x vector for each ensemble.
 *  @param b output RHS ensemble (ensemblecount*M).
 *  @return Void.
 */
void formRHS(double** A, int M, int N, int ensemblecount, int wantindependentensemble ,double **b);

/** @brief Use A and a random x to create an ensemble of RHS vector that is ensemblecount in size.
 *  @param A src matrix (M*N) CSR matrix.
 *  @param M #rows in the matrix.
 *  @param N #cols in the matrix.
 *  @param ensemblecount #entires in the ensemble.
 *  @param wantindependentensemble <0|1>. If true, create a new x vector for each ensemble.
 *  @param b output RHS ensemble (M*ensemblecount).
 *  @return Void.
 */
void formRHSTranspose(double** A, int M, int N, int ensemblecount, int wantindependentensemble ,double **b);

/** @brief Printout the output.
 *  @param converged .
 *  @param normval.
 *  @param ensemblecount.
 *  @return Void.
 */
void output(int *converged, double * normval, int ensemblecount);
#endif
