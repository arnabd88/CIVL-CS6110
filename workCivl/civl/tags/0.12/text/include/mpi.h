#ifdef __MPI__
#else
#define __MPI__
#include<civlc.h>

typedef enum {
    MPIX_NO_OP,
    MPI_MAX, 
    MPI_MIN,     
    MPI_SUM,
    MPI_PROD,
    MPI_LAND,   
    MPI_BAND,   
    MPI_LOR,     
    MPI_BOR,     
    MPI_LXOR,    
    MPI_BXOR,    
    MPI_MINLOC,  
    MPI_MAXLOC,  
    MPI_REPLACE
}MPI_Op;

/* Temporary use */
#define MPI_NO_OP   CIVL_NO_OP
#define MPI_MAX     CIVL_MAX   
#define MPI_MIN     CIVL_MIN    
#define MPI_SUM     CIVL_SUM
#define MPI_PROD    CIVL_PROD    
#define MPI_LAND    CIVL_LAND   
#define MPI_BAND    CIVL_BAND
#define MPI_LOR     CIVL_LOR
#define MPI_BOR     CIVL_BOR
#define MPI_LXOR    CIVL_LXOR
#define MPI_BXOR    CIVL_BXOR
#define MPI_MINLOC  CIVL_MINLOC
#define MPI_MAXLOC  CIVL_MAXLOC
#define MPI_REPLACE CIVL_REPLACE

#include<mpi-common.h>
#include<mpi.cvl>
#endif
