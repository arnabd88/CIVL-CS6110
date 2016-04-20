#include <mpi.h>
#include <stdio.h>
#ifdef _CIVL
#include<civlc.cvh>
#endif

#define WCOMM MPI_COMM_WORLD

int main(int argc, char **argv){
    int npes, mype, ierr;
    double sum[2], val[2]; int calc, knt=1;
    ierr = MPI_Init(&argc, &argv);
    ierr = MPI_Comm_size(WCOMM, &npes);
    ierr = MPI_Comm_rank(WCOMM, &mype);
    
    val[0]  = (double)mype;
    val[1]  = (double)mype;
#ifdef OPERATOR
    if(mype%2)
        ierr = MPI_Reduce(val, sum, knt, MPI_DOUBLE, MPI_SUM, 0, WCOMM);
    else
        ierr = MPI_Reduce(val, sum, knt, MPI_DOUBLE, MPI_MAX, 0, WCOMM);
#elif defined ORDER
    if(mype !== 2)
        ierr = MPI_Reduce(val, sum, knt, MPI_DOUBLE, MPI_SUM, 0, WCOMM);
#elif defined TYPE
    if(mype%2)
        ierr = MPI_Reduce(val, sum, knt, MPI_DOUBLE, MPI_SUM, 0, WCOMM);
    else
        ierr = MPI_Reduce(val, sum, knt, MPI_INT, MPI_SUM, 0, WCOMM);
#elif defined ROOT
    ierr = MPI_Reduce(val, sum, knt, MPI_DOUBLE, MPI_SUM, mype, WCOMM);
#elif defined COUNT
    knt = 2-(mype%2);
    ierr = MPI_Reduce(val, sum, knt, MPI_DOUBLE, MPI_SUM, 0, WCOMM);
#else
    ierr = MPI_Reduce(val, sum, knt, MPI_DOUBLE, MPI_SUM, 0, WCOMM);
#endif
    
    calc = ((npes - 1) * npes) / 2;
    if(mype == 0){
        printf(" PE: %d sum=%5.0f calc=%d\n", mype, sum[0], calc);
#ifdef _CIVL
#ifndef OPERATOR
        $assert(sum[0] == calc);
#endif
#endif
    }
    ierr = MPI_Finalize();
}
