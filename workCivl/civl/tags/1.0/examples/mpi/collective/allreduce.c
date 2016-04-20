#include <mpi.h>
#include <stdio.h>
#ifdef _CIVL
#include<civlc.cvh>
#endif

#define WCOMM MPI_COMM_WORLD

int main(int argc, char **argv){
    int npes, mype, ierr;
    double sum, val; int calc, knt=1;
    ierr = MPI_Init(&argc, &argv);
    ierr = MPI_Comm_size(WCOMM, &npes);
    ierr = MPI_Comm_rank(WCOMM, &mype);
    
    val  = (double)mype;
    
#ifdef TYPE
    if(mype%2)
        ierr = MPI_Allreduce(&val, &sum, knt, MPI_DOUBLE, MPI_SUM, WCOMM);
    else
        ierr = MPI_Allreduce(&val, &sum, knt, MPI_INT, MPI_SUM, WCOMM);
#elif defined OPERATOR
    if(mype%2)
        ierr = MPI_Allreduce(&val, &sum, knt, MPI_DOUBLE, MPI_SUM, WCOMM);
    else
        ierr = MPI_Allreduce(&val, &sum, knt, MPI_DOUBLE, MPI_MAX, WCOMM);
#else
    ierr = MPI_Allreduce(&val, &sum, knt, MPI_DOUBLE, MPI_SUM, WCOMM);
#endif
    
    calc = ((npes - 1) * npes) / 2;
    printf(" PE: %d sum=%5.0f calc=%d\n", mype, sum, calc);
#ifdef _CIVL
#ifndef OPERATOR
    $assert(sum == calc);
#endif
#endif
    ierr = MPI_Finalize();
}
