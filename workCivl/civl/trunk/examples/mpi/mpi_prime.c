#ifdef _CIVL
#include <civlc.cvh>
#endif
/*
 * mpi_prime.c: parallel prime numbers generator within a limited
 * numbers.  
 * To execute: mpicc mpi_prime.c ; mpiexec -n 4 ./a.out Or
 * replace "4" with however many procs you want to use.  
 * To verify: civl verify wave1d.c
 *
 * Modified from the original program: mpi_prime.c
 * Source: https://computing.llnl.gov/tutorials/mpi/samples/C/mpi_prime.c
 */
#include <assert.h>
#include <mpi.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>

#define FIRST 0                             // rank of the first process
#ifdef _CIVL
$input int _mpi_nprocs_lo = 1;
$input int _mpi_nprocs_hi = 4;
$input int LIMITB = 15;                     // upper bound of LIMITS
$input int LIMIT;                           // upper bound of searching numbers
$assume(10 < LIMIT && LIMIT <= LIMITB);
/* results of sequential run with initializers. The first element
   stores the number of found prime numbers, the second element stores
   the largest found prime number. */
int oracle[2] = {4, 0};  
#else
#define LIMIT 800
#endif

/* Returns 1 if the given number n is a prime number, else returns 0 */
int isprime(int n) {
  int i,squareroot;

  if (n>10) {
    squareroot = (int) sqrt(n);
    for (i=3; i<=squareroot; i=i+2)
      if ((n%i)==0)
	return 0;
    return 1;
  }
  /* Assume first four primes are counted elsewhere. Forget everything else */
  else
    return 0;
}

#ifdef _CIVL
/* sequential run for finding prime numbers within the limited number,
   saving results */
void seq_run() {
  for (int n=3; n<=LIMIT; n=n+2) {
    if (isprime(n)) {
      oracle[0]++;
      oracle[1] = n;
    }
  }
}
#endif

int main (int argc, char *argv[])
{
  int   
    ntasks,               /* total number of tasks in partitiion */
    rank,                 /* task identifier */
    n,                    /* loop variable */
    pc,                   /* prime counter */
    pcsum,                /* number of primes found by all tasks */
    foundone,             /* most recent prime found */
    maxprime,             /* largest prime found */
    mystart,              /* where to start calculating */
    stride;               /* calculate every nth number */
  double start_time,end_time;
	
  MPI_Init(&argc,&argv);
  MPI_Comm_rank(MPI_COMM_WORLD,&rank);
  MPI_Comm_size(MPI_COMM_WORLD,&ntasks);
  if (((ntasks%2) !=0) || ((LIMIT%ntasks) !=0)) {
    printf("Sorry - this exercise requires an even number of tasks.\n");
    printf("number of tasks %d should be evenly divisible into %d. "
	   " Try 4 or 8.\n",ntasks, LIMIT);
    MPI_Finalize();
    return 0;
  }
  start_time = MPI_Wtime();   /* Initialize start time */
  mystart = (rank*2)+1;       /* Find my starting point - must be odd number */
  stride = ntasks*2;          /* Determine stride, skipping even numbers */
  pc=0;                       /* Initialize prime counter */
  foundone = 0;               /* Initialize */
  
  /******************** task with rank 0 does this part ********************/
  if (rank == FIRST) {
#ifdef _CIVL
    seq_run();
#endif
    printf("Using %d tasks to scan %d numbers\n",ntasks,LIMIT);
    pc = 4;                  /* Assume first four primes are counted here */
    for (n=mystart; n<=LIMIT; n=n+stride) {
      if (isprime(n)) {
	pc++;
	foundone = n;
	/***** Optional: print each prime as it is found
	       printf("%d\n",foundone);
	*****/
      }
    }
    MPI_Reduce(&pc,&pcsum,1,MPI_INT,MPI_SUM,FIRST,MPI_COMM_WORLD);
    MPI_Reduce(&foundone,&maxprime,1,MPI_INT,MPI_MAX,FIRST,MPI_COMM_WORLD);
    end_time=MPI_Wtime();
#ifdef _CIVL
  $assert((pcsum == oracle[0]), "The calculated number of prime numbers is %d"
      " but the expected number is %d with a limit of %d\n",pcsum, oracle[0], LIMIT);
  $assert((maxprime == oracle[1]), "The Largest prime is %d but the expected "
      "one is %d with a limit of %d\n",maxprime, oracle[1], LIMIT);
#endif
    printf("Done. Largest prime is %d Total primes %d\n",maxprime,pcsum);
    printf("Wallclock time elapsed: %.2lf seconds\n",end_time-start_time);
  }


  /******************** all other tasks do this part ***********************/
  if (rank > FIRST) {
    for (n=mystart; n<=LIMIT; n=n+stride) {
      if (isprime(n)) {
	pc++;
	foundone = n;
	/***** Optional: print each prime as it is found
	       printf("%d\n",foundone);
	*****/
      }
    }
    MPI_Reduce(&pc,&pcsum,1,MPI_INT,MPI_SUM,FIRST,MPI_COMM_WORLD);
    MPI_Reduce(&foundone,&maxprime,1,MPI_INT,MPI_MAX,FIRST,MPI_COMM_WORLD);
  }

  MPI_Finalize();
}
