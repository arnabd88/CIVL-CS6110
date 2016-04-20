#ifdef _CIVL
#include <civlc.cvh>
#endif
/**********************************************************************
			ProMCore 2008 
		    February 05 - 09, 2008


 Example 1.2      : mpi-Pthreads-pie-collective.c
    
 Objective        : Write an MPI-Pthreads program to compute the value
                    of PI by numerical integration of a function f(x)
                    =4/(1+x*x) between the limits 0 and 1.Pthreads and 
                    MPI Collective communication library calls are used.

                    This example demonstrates the use of

                    pthread_create()
                    pthread_join()
                    pthread_mutex_lock()
                    pthread_mutex_unlock()
 
                    MPI_Init 
                    MPI_Comm_rank 
                    MPI_Comm_size 
                    MPI_Bcast 
                    MPI_Reduce 
                    MPI_Finalize

 Input             : Number of Intervals.

 Output            : Calculated Value of PI.

 Created	   : January 2008                                              
               	     National PARAM Supercomputing Facility,C-DAC,Pune.        

 
 E-mail      	   : betatest@cdac.in                                          

************************************************************************/

#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include "mpi.h"
#include <pthread.h>

#ifdef _CIVL
$input int NUM_INTERVAL_BOUND = 4;
#endif

double  intervalWidth, mypi = 0.0;
int     *MyIntervals;
int     MyRank, Numprocs, Root = 0, MyCount = 0;
pthread_mutex_t mypi_mutex = PTHREAD_MUTEX_INITIALIZER;

void * MyPartOfCalc(int myID)
{
	int    myInterval;
	double  myIntervalMidPoint;
	double  myArea = 0.0, result;

	myIntervalMidPoint = ((double) MyIntervals[myID] - 0.5) * intervalWidth;
	myArea += (4.0 / (1.0 + myIntervalMidPoint * myIntervalMidPoint));

	result = myArea * intervalWidth;

	/* Lock the mutex controlling the access to area. */

	pthread_mutex_lock(&mypi_mutex);
	mypi += result;
	pthread_mutex_unlock(&mypi_mutex);
}

double func(double x)
{
	return (4.0 / (1.0 + x * x));
}

int main(int argc, char *argv[])
{
	int             NoInterval, interval, i;
	double          pi, sum, h, x;
	double          PI25DT = 3.141592653589793238462643;
	pthread_t      *threads;

	/* ....MPI initialisation.... */
	MPI_Init(&argc, &argv);
	MPI_Comm_size(MPI_COMM_WORLD, &Numprocs);
	MPI_Comm_rank(MPI_COMM_WORLD, &MyRank);

	if (MyRank == Root) {
		printf("\nEnter the number of intervals : ");
		scanf("%d", &NoInterval);
	       	#ifdef _CIVL
		$assume(NoInterval <= NUM_INTERVAL_BOUND);
                #endif
	}

	/* ....Broadcast the number of subintervals to each processor.... */
	MPI_Bcast(&NoInterval, 1, MPI_INT, 0, MPI_COMM_WORLD);
        #ifdef _CIVL
	$assume(NoInterval > 0);
	#endif
	if (NoInterval <= 0) {
		if (MyRank == Root)
			printf("Invalid Value for Number of Intervals .....\n");
		MPI_Finalize();
		exit(-1);
	}
	h = 1.0 / (double) NoInterval;
	intervalWidth = h;

	/* Start Calcualtions to determine the number of intervals for each */
	/* processes of the Communicator. */

	MyCount = 0;
	for (interval = MyRank + 1; interval <= NoInterval; interval += Numprocs)
		MyCount++;

	MyIntervals = (int *) malloc(sizeof(int) * MyCount);

	for (i = 0, interval = MyRank + 1; interval <= NoInterval; i++, interval += Numprocs)
		MyIntervals[i] = interval;

	/* Start creating threads. */

	threads = (pthread_t *) malloc(sizeof(pthread_t) * MyCount);

	for (interval = 0; interval < MyCount; interval++)
		pthread_create(&threads[interval], NULL, (void *(*) (void *)) MyPartOfCalc, (void *) interval);

	for (interval = 0; interval < MyCount; interval++)
		pthread_join(threads[interval], NULL);

	/* ....Collect the areas calculated in P0.... */
	MPI_Reduce(&mypi, &pi, 1, MPI_DOUBLE, MPI_SUM, Root, MPI_COMM_WORLD);

	if (MyRank == Root) {
		printf("pi is approximately %.16f, Error is %.16f\n",
		       pi, fabs(pi - PI25DT));
	}
	free(threads);
	free(MyIntervals);
	MPI_Finalize();

}
