
	

/**********************************************************************
                   C-DAC Tech Workshop : hyPACK-2013
                             Oct 15-18,2013

 Example 1.1   : Mpi-Pthreads-Helloworld.C

 Objective     : Write An Mpi-Pthreads Program To Print Hello World! 

                    Demonstrates Use Of:
                    Pthread_Create()
                    Pthread_Join()
                    Mpi_Init
                    Mpi_Comm_Rank 
                    Mpi_Comm_Size
                    Mpi_Finalize 

 Input          : None.

 Output         : Hello World From Thread: Thread No. On Process:
	          Process No.

 Created        : MAY-2013    

 E-Mail      	: hpcfte@cdac.in                                          

************************************************************************/ 


/* A Simple Hello World In Mpi-Pthreads. */

#include <pthread.h> 
#include "mpi.h"
#include <stdio.h>


int   Myrank, Numprocs;

void   * Work(int Myid)
{
    printf(" Hello World! From Thread:%d On Process: %d. \n", Myid, Myrank);
    return NULL;
}

void main(int Argc, char *Argv[])
{
	pthread_t  Thread1, Thread2;

	MPI_Status  Status;

	/* Initialize Mpi Environment. */

	MPI_Init(&Argc, &Argv);
	MPI_Comm_size(MPI_COMM_WORLD, &Numprocs);
	MPI_Comm_rank(MPI_COMM_WORLD, &Myrank);


	pthread_create(&Thread1, NULL, (void *(*) (void *)) Work, (void *) 1);

	pthread_create(&Thread2, NULL, (void *(*) (void *)) Work, (void *) 2);

	pthread_join(Thread1, NULL);
	pthread_join(Thread2, NULL);

	MPI_Finalize();

	return;

}
