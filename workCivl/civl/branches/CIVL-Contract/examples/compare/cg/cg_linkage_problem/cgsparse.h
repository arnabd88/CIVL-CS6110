//
//  cgsparse.h
//  cgnonintrusive
//
//  Created by Sri Hari Krishna Narayanan on 11/10/15.
//
//

#ifndef __cg__cgsparse_h
#define __cg__cgsparse_h

/** @brief Fully intrusive version of CSR CG algorithm. Solves Ax=b for an ensemble of A in CSR format and a single b and returns x for each ensemble member and the iteration at which convergence is reached.
 *  @param NZ #nonzeroes in each CSR matrix.
 *  @param row_start rows of each CSR matrix.
 *  @param col_idx cols of each CSR matrix.
 *  @param CSR_A values of the ensemble of CSR matrices.
 *  @param b RHS vector.
 *  @param n dimensions of A (same as m).
 *  @param m dimensions of A (same as n).
 *  @param tolerance value to which norm is tested.
 *  @param ensemblecount number of ensembles, .
 *  @param ensemblepolicy (allconverge=0, anyconverge=1, halfconverge=2).
 *  @param x ensemble of output solutions.
 *  @param converged output to report iterations at which CG converges.
 *  @return Void.
 */
void conjugateGradientEnsembleACSR( int NZ, int *row_start, int *col_idx, double **CSR_A, double *b, int n, int m, double tolerance, int ensemblecount, int ensemblepolicy, double **x, int *converged);

/** @brief Fully intrusive version of CSR CG algorithm. Solves Ax=b for a single A in CSR format and an ensemble of b and returns x for each ensemeble member and the iteration at which convergence is reached.
 *  @param NZ #nonzeroes in the CSR matrix.
 *  @param row_start rows of the CSR matrix.
 *  @param col_idx cols of the CSR matrix.
 *  @param CSR_A values of the CSR matrix.
 *  @param ensemble of b RHS vectors.
 *  @param n dimensions of A (same as m).
 *  @param m dimensions of A (same as n).
 *  @param tolerance value to which norm is tested.
 *  @param ensemblecount number of ensembles, .
 *  @param ensemblepolicy (allconverge=0, anyconverge=1, halfconverge=2).
 *  @param x ensemble of output solutions.
 *  @param converged output to report iterations at which CG converges.
 *  @return Void.
 */
void conjugateGradientEnsembleBCSR(int NZ, int *row_start, int *col_idx, double *CSR_A, double **b, int n, int m, double tolerance, int ensemblecount, int ensemblepolicy, double **x, int *converged);

/** @brief Generates an ensemble of CSR A matrices and solves CSR CG fully intrusively.
 *  @param filename file containing an input A matrix (can be NULL).
 *  @param rhsfilename file containing an input RHS (can be NULL).
 *  @param directionfilename file containing an input direction vector (can be NULL).
 *  @param scalingfactor value used to scale diagonal entries of A matrices of ensemble.
 *  @param tolerance value to which norm is tested.
 *  @param ensemblecount total number of ensembles.
 *  @param ensemblepolicy (allconverge=0, anyconverge=1, halfconverge=2).
 *  @param wantindependentensemble boolean to test if ensembles should be independent from each other.
 *  @return Void.
 */
void solveEnsembleACSR(const char * filename, const char * rhsfilename, const char * directionfilename, double scalingfactor, double tolerance, int ensemblecount, int ensemblepolicy, int wantindependentensemble);

/** @brief Generates an ensemble of RHS vectors and solves CSR CG fully instrusively.
 *  @param filename file containing an input A matrix (can be NULL).
 *  @param rhsfilename file containing an input RHS (can be NULL).
 *  @param directionfilename file containing an input direction vector (can be NULL).
 *  @param scalingfactor value used to scale RHS vectors of ensemble.
 *  @param tolerance value to which norm is tested.
 *  @param ensemblecount total number of ensembles.
 *  @param ensemblepolicy (allconverge=0, anyconverge=1, halfconverge=2).
 *  @param wantindependentensemble boolean to test if ensembles should be independent from each other.
 *  @return Void.
 */
void solveEnsembleBCSR(const char * filename, const char * rhsfilename, const char * directionfilename, double scalingfactor, double tolerance, int ensemblecount, int ensemblepolicy, int wantindependentensemble);

#endif
