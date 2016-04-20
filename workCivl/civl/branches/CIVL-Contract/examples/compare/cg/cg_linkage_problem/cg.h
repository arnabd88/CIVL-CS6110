//
//  cg.h
//  cg
//
//  Created by Sri Hari Krishna Narayanan on 5/21/15.
//
//

#ifndef __cg__cg__
#define __cg__cg__

/** @brief Fully intrusive version of CG algorithm. Solves Ax=b for an ensemble of A and a single b and returns x for each ensemble member and the iteration at which convergence is reached.
 *  @param A ensemble of A matrices.
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
void conjugateGradientEnsembleA( double ***A, double *b, int n, int m, double tolerance, int ensemblecount, int ensemblepolicy, double **x, int *converged);

/** @brief Fully intrusive version of CG algorithm. Solves Ax=b for a single A and an ensemble of b and returns x for each ensemeble member and the iteration at which convergence is reached.
 *  @param A A matrix.
 *  @param b ensemble of RHS vectors.
 *  @param n dimensions of A (same as m).
 *  @param m dimensions of A (same as n).
 *  @param tolerance value to which norm is tested.
 *  @param ensemblecount number of ensembles, .
 *  @param ensemblepolicy (allconverge=0, anyconverge=1, halfconverge=2).
 *  @param x ensemble of output solutions.
 *  @param converged output to report iterations at which CG converges.
 *  @return Void.
 */
void conjugateGradientEnsembleB( double **A, double **b, int n, int m, double tolerance, int ensemblecount, int ensemblepolicy, double **x, int *converged);

/** @brief Generates an ensemble of A matrices and solves CG fully intrusively.
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
void solveEnsembleA(const char * filename, const char * rhsfilename, const char * directionfilename, double scalingfactor, double tolerance, int ensemblecount, int ensemblepolicy, int wantindependentensemble);

/** @brief Generates an ensemble of RHS vectors and solves CG fully instrusively.
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
void solveEnsembleB(const char * filename, const char * rhsfilename, const char * directionfilename, double scalingfactor, double tolerance, int ensemblecount, int ensemblepolicy, int wantindependentensemble);

void usage();

#endif /* defined(__cg__cg__) */
