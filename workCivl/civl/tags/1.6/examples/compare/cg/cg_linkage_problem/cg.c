//
//  cg.c
//  cg
//
//  Created by Sri Hari Krishna Narayanan on 5/21/15.
//
//

#include <time.h>
#include <ctype.h>
#include <stdio.h>
#include <unistd.h>
#include <stdlib.h>
#include <math.h>
#include <assert.h>
#include "cg.h"
#include "cgsparse.h"
#include "mmio.h"
#include "utils.h"

void conjugateGradientEnsembleA( double ***A, double *b, int n, int m, double tolerance, int ensemblecount, int ensemblepolicy, double **x, int *converged){
    double **r, **p, **q, *alpha, **Ax, *rho, *rhoold, *rhotemp, **s, **Axminusb;
    int k = 0, i, j, e, shouldcontinue;
    r = createMatrix(ensemblecount, m);
    s = createMatrix(ensemblecount, m);
    p = createMatrix(ensemblecount, m);
    q = createMatrix(ensemblecount, m);
    rho = (double *) malloc (ensemblecount *sizeof(double));
    rhoold = (double *) malloc (ensemblecount *sizeof(double));
    rhotemp= (double *) malloc (ensemblecount *sizeof(double));
    alpha = (double *) malloc (ensemblecount *sizeof(double));
    Ax = createMatrix(ensemblecount,m);
    Axminusb = createMatrix(ensemblecount, m);
    for(e =0; e<ensemblecount; e++)
      for(i = 0; i < n ; i++)
        x[e][i] =0.0;
    for(e =0; e<ensemblecount; e++) {
      matrixVectorProduct(A[e], x[e], n, m, Ax[e]);
      vectorDifference(b, Ax[e], n, r[e]);
    }
    for(e =0; e<ensemblecount; e++)
      for(i = 0; i < n ; i++)
        p[e][i] = r[e][i]/A[e][i][i];
    matrixCopy(p, ensemblecount, n, s);
    vectorVectorTransposeProductInsideMatrix(r, p, ensemblecount, n, rho);
    shouldcontinue = !haveConvergedPerRow(r, b, ensemblecount, n, ensemblepolicy, tolerance, k, converged);
    while (shouldcontinue){
        //printf("\n k = %d shouldcontinue = %d", k, shouldcontinue);
        for(e =0; e<ensemblecount; e++)
          matrixVectorProduct(A[e], s[e], n, m, q[e]);
        vectorVectorTransposeProductInsideMatrix(s, q, ensemblecount, n, rhotemp);
        for(e =0; e<ensemblecount; e++)
            alpha[e] = rho[e]/rhotemp[e];
        for(e =0; e<ensemblecount; e++)
          for(i = 0; i < n ; i++)
            x[e][i] = x[e][i] + alpha[e] * s[e][i];
        for(e =0; e<ensemblecount; e++)
          for(i = 0; i < n ; i++)
            r[e][i] = p[e][i] - alpha[e] * q[e][i];
        for(e =0; e<ensemblecount; e++)
          for(i = 0; i < n ; i++)
            p[e][i] = r[e][i]/A[e][i][i];
        vectorCopy(rho,ensemblecount,rhoold);
        vectorVectorTransposeProductInsideMatrix(r, p, ensemblecount, n, rho);
        for(e =0; e<ensemblecount; e++)
          for(i = 0; i < n ; i++)
            s[e][i] = p[e][i] - rho[e]/rhoold[e] * s[e][i];
        for(e =0; e<ensemblecount; e++) {
          matrixVectorProduct(A[e], x[e], n, m, Ax[e]);
          vectorDifference(b, Ax[e], n, Axminusb[e]);
        }
        k++;
        shouldcontinue = !haveConvergedPerRow(r, b, ensemblecount, n, ensemblepolicy, tolerance, k, converged);
    }
    destroyMatrix(r,ensemblecount);
    destroyMatrix(s,ensemblecount);
    destroyMatrix(p,ensemblecount);
    destroyMatrix(q,ensemblecount);
    destroyMatrix(Axminusb,ensemblecount);
    destroyMatrix(Ax,ensemblecount);
    free(rho);
    free(rhoold);
    free(rhotemp);
    free(alpha);
}

void solveEnsembleA(const char * filename, const char * rhsfilename, const char * directionfilename, double scalingfactor, double tolerance, int ensemblecount, int ensemblepolicy, int wantindependentensemble){
    time_t  t0, t1;
    clock_t c0, c1;
    int *I, *J, M, N, Mb, NZ, *converged;
    double *val, *valb=NULL;
    double **A, ***Aensemble, **b, **x, *normval;
    int i,j,k, rhsensemblecount=1;
    //Read in a matrix
    int ret = mm_read_symmetric_sparse(filename, &M, &N, &NZ, &val, &I, &J);
    if(ret !=0) {
        fprintf (stderr, "\n Error in reading file %s.\n", filename);
        return;
    }
    if(rhsfilename!=NULL) {
        ret = createRHSMatrix(&b, &Mb, &rhsensemblecount, rhsfilename, NULL, 1.0);
        if( M!=Mb){
            fprintf (stderr, "\n Matrix file row information does not match RHS file information M = %d, Mb = %d\n", M, Mb);
            return;
        }
    } else
        ret = createRHSMatrix(&b, &M, &rhsensemblecount, rhsfilename, NULL, 1.0);
    if(ret!=0)
        return;
    A = createMatrix(M, N);
    x = createMatrix(ensemblecount,M);
    for(i = 0; i < NZ ; i++){
        A[I[i]][J[i]] = val[i];
    }
    for(i = 0; i < N ; i++)
        A[i][i] += 1.0;
    
    diagonalPreconditioner(A, N, M);
    
    if(rhsfilename==NULL)
      formRHS(A, M, N, rhsensemblecount, wantindependentensemble, b);
    
    ret = createMatrixEmsemble(A, M, ensemblecount, directionfilename, scalingfactor, &Aensemble); 
    if(ret!=0)
        return;
    converged = (int*) malloc (N*sizeof(int));
    for(i = 0; i < ensemblecount ; i++)
      converged[i] = -1;
    t0 = time(NULL);
    c0 = clock();
    conjugateGradientEnsembleA(Aensemble, b[0], M, N, tolerance, ensemblecount, ensemblepolicy, x, converged);
    t1 = time(NULL);
    c1 = clock();
    
    normval = (double*) malloc (N*sizeof(double));
    norm2PerRow(x, ensemblecount, N, normval); 
    for(i = 0; i < ensemblecount ; i++){
      if(converged[i]>=0){
        printf ("\tnorm2(x[%d]^2):             %lg, converged in %d \n", i, normval[i]*normval[i], converged[i]);
	FILE* fh=fopen("norm.out","a+");
        fprintf (fh,"%.16e %d\n",normval[i]*normval[i], converged[i]);
	fclose(fh);
      } else 
        printf ("\tnorm2(x[%d]^2):             NC\n", i);
    }
    
    for(i = 0; i < ensemblecount ; i++)
      destroyMatrix(Aensemble[i], M);
    free(Aensemble);
    destroyMatrix(A, M);
    destroyMatrix(b, rhsensemblecount);
    destroyMatrix(x, ensemblecount);
    free(val);
    free(I);
    free(J);
    free(converged);
    free(normval);

    printf ("\tend A (wall):                 %ld\n", (long) t1);
    printf ("\tend A (CPU);                  %d\n", (int) c1);
    printf ("\telapsed wall clock time(s): %ld\n", (long) (t1 - t0));
    printf ("\telapsed CPU time (s):       %f\n", (float) (c1 - c0)/CLOCKS_PER_SEC);
}

void conjugateGradientEnsembleB( double **A, double **b, int n, int m, double tolerance, int ensemblecount, int ensemblepolicy, double **x, int *converged){
    double **r, **p, **q, *alpha, **Ax, **Ainv, *rho, *rhoold, *rhotemp, **s, **Axminusb;
    int k = 0, i, j, e, shouldcontinue;
    r = createMatrix(m,ensemblecount);
    s = createMatrix(m,ensemblecount);
    p = createMatrix(m,ensemblecount);
    q = createMatrix(m,ensemblecount);
    rho = (double *) malloc (ensemblecount *sizeof(double));
    rhoold = (double *) malloc (ensemblecount *sizeof(double));
    rhotemp= (double *) malloc (ensemblecount *sizeof(double));
    alpha = (double *) malloc (ensemblecount *sizeof(double));
    Ax = createMatrix(m,ensemblecount);
    Axminusb = createMatrix(m,ensemblecount);
    for(i = 0; i < n ; i++)
        for(e =0; e<ensemblecount; e++)
          x[i][e] =0.0;
    matrixMatrixProduct(A, x, n, m, ensemblecount, Ax);
    matrixDifference(b, Ax, n, ensemblecount, r);
    for(i = 0; i < n ; i++)
      for(e =0; e<ensemblecount; e++)
        p[i][e] = r[i][e]/A[i][i];
    matrixCopy(p, n, ensemblecount, s);
    vectorTransposeVectorProductInsideMatrix(r, p, n, ensemblecount, rho);
    shouldcontinue = !haveConvergedPerColumn(r, b, n, ensemblecount, ensemblepolicy, tolerance, k, converged);
    while (shouldcontinue){
        //printf("\n k = %d shouldcontinue = %d", k, shouldcontinue);
        matrixMatrixProduct(A, s, n, m, ensemblecount, q);
        vectorTransposeVectorProductInsideMatrix(s, q, n, ensemblecount,rhotemp);
        for(e =0; e<ensemblecount; e++)
            alpha[e] = rho[e]/rhotemp[e];
        for(i = 0; i < n ; i++)
          for(e =0; e<ensemblecount; e++)
            x[i][e] = x[i][e] + alpha[e] * s[i][e];
        for(i = 0; i < n ; i++)
          for(e =0; e<ensemblecount; e++)
            r[i][e] = p[i][e] - alpha[e] * q[i][e];
        for(i = 0; i < n ; i++)
          for(e =0; e<ensemblecount; e++)
            p[i][e] = r[i][e]/A[i][i];
        vectorCopy(rho,ensemblecount,rhoold);
        vectorTransposeVectorProductInsideMatrix(r, p, n, ensemblecount,rho);
        for(i = 0; i < n ; i++)
          for(e =0; e<ensemblecount; e++)
            s[i][e] = p[i][e] - rho[e]/rhoold[e] * s[i][e];
        matrixMatrixProduct(A, x, n, m, ensemblecount, Ax),
        matrixDifference(b, Ax, n, ensemblecount, Axminusb);
        k++;
        shouldcontinue = !haveConvergedPerColumn(Axminusb, b, n, ensemblecount, ensemblepolicy, tolerance, k, converged);
    }
    destroyMatrix(r,m);
    destroyMatrix(s,m);
    destroyMatrix(p,m);
    destroyMatrix(q,m);
    destroyMatrix(Axminusb,m);
    destroyMatrix(Ax,m);
    free(rho);
    free(rhoold);
    free(rhotemp);
    free(alpha);
}

void solveEnsembleB(const char * filename, const char * rhsfilename, const char * directionfilename, double scalingfactor, double tolerance, int ensemblecount, int ensemblepolicy, int wantindependentensemble){
    time_t  t0, t1;
    clock_t c0, c1;
    int *I, *J, M, N, Mb, NZ, *converged;
    double *val, *valb=NULL;
    double **A, **b, **x, *normval;
    int i,j,k;
    //Read in a matrix
    int ret = readMatrixFile(filename, &M, &N, &NZ, &val, &I, &J);
    if(ret !=0) {
        fprintf (stderr, "\n Error in reading file %s.\n", filename);
        return;
    }
    if(rhsfilename!=NULL) {
        ret = createRHSMatrixTranspose(&b, &Mb, &ensemblecount, rhsfilename, directionfilename, scalingfactor);
        if( M!=Mb){
            fprintf (stderr, "\n Matrix file row information does not match RHS file information M = %d, Mb = %d\n", M, Mb);
            return;
        }
    } else
        ret = createRHSMatrixTranspose(&b, &M, &ensemblecount, rhsfilename, directionfilename, scalingfactor);
    if(ret!=0)
        return;
    A = createMatrix(M, N);
    x = createMatrix(M, ensemblecount);
    for(i = 0; i < NZ ; i++){
        A[I[i]][J[i]] = val[i];
    }
    for(i = 0; i < N ; i++)
        A[i][i] += 1.0;
    
    diagonalPreconditioner(A, N, M);
    
    if(rhsfilename==NULL)
      formRHSTranspose(A, M, N, ensemblecount, wantindependentensemble, b);
    converged = (int *) malloc (N*sizeof(int));
    for(i = 0; i < ensemblecount ; i++)
      converged[i] = -1;
    
    t0 = time(NULL);
    c0 = clock();
    conjugateGradientEnsembleB(A, b, M, N, tolerance, ensemblecount, ensemblepolicy, x, converged);
    t1 = time(NULL);
    c1 = clock();
    
    normval = (double*) malloc (N*sizeof(double));
    norm2PerColumn(x, N, ensemblecount, normval); 
    for(i = 0; i < ensemblecount ; i++){
      if(converged[i]>=0){
        printf ("\tnorm2(x[%d]^2):             %lg, converged in %d \n", i, normval[i]*normval[i], converged[i]);
	FILE* fh=fopen("norm.out","a+");
        fprintf (fh,"%.16e %d\n",normval[i]*normval[i], converged[i]);
	fclose(fh);
      } else 
        printf ("\tnorm2(x[%d]^2):             NC\n", i);
    }

    destroyMatrix(A, M);
    destroyMatrix(b, M);
    destroyMatrix(x, M);
    free(val);
    free(I);
    free(J);
    free(converged);
    free(normval);

    printf ("\tend b (wall):                 %ld\n", (long) t1);
    printf ("\tend b (CPU);                  %d\n", (int) c1);
    printf ("\telapsed wall clock time(s): %ld\n", (long) (t1 - t0));
    printf ("\telapsed CPU time (s):       %f\n", (float) (c1 - c0)/CLOCKS_PER_SEC);
}
