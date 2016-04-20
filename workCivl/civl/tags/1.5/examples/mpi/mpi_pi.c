#ifdef _CIVL
#include <civlc.cvh>
#endif
/* FILENAME: mpi_pi.c */
/* Calculating value of pi using a "dartboard" algorithm. In CIVL
 * mode, the program will first let process of rank 0 do a sequential
 * run and the results of it will be used to compare with the result
 * of each round during parallel run. 
 * To execute: mpicc mpi_pi.c && mpiexec -n 4 ./a.out 
 * Here '4' can be replaced by any number.
 * To verify: civl verify mpi_pi.c
 *
 * Modified from the original program: mpi_pi_send.c
 * Source: https://computing.llnl.gov/tutorials/mpi/samples/C/mpi_pi_send.c */
#include <mpi.h>
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

#define MASTER 0
#define SQR(X) ((X)*(X))

#ifdef _CIVL
const int DARTSB = 2;         // upper bound of DARTS
$input int DARTS;             // number of darts will be throwed
$assume(0 < DARTS && DARTS <= DARTSB);
const int ROUNDSB = 2;        // upper bound of ROUNDS
$input int ROUNDS;            // number of rounds of throwing darts
$assume(0 < ROUNDS && ROUNDS <= ROUNDSB);
$input int _mpi_nprocs = 2;
$input int N;                 // length of random data array
$input double RANDOM[N];      // random data array
double oracle[ROUNDS];        // array of results of sequential run

/* CIVL mode rand() function: returns unconstrained value as a random
   number for a specific process throwing a specific dart right at the
   given round. So that the sequential version and parallel version
   are guaranteed to compute with a same set of ordered random
   data. */
double civlrand(int dart, int taskid, int curr_round) {
  return RANDOM[taskid * (ROUNDS * DARTS) + dart * ROUNDS + curr_round];
}
#else
int DARTS, ROUNDS;
#endif
int curr_round;              // current round 
int taskid;                  // the identity of a task which is 
                             // a process in parallel run.
int tasks;                   // the number of tasks whichis the number
                             // of processes in parallel run

/***********************************************************************
 * Throw darts at board.  Done by generating random numbers
 * between 0 and 1 and converting them to values for x and y
 * coordinates and then testing to see if they "land" in
 * the circle."  If so, score is incremented.  After throwing the
 * specified number of darts, pi is calculated.  The computed value
 * of pi is returned as the value of this function, dboard.
 ************************************************************************/
double dboard(int darts, int taskid) {
  double x_coord,       // x coordinates, between -1 and 1
         y_coord,       // y coordinates, between -1 and 1
         pi,            // pi
         rx,            // random number for x coordinate
         ry;            // random number for y coordinate
  int score,            // number of darts hit the circle
      n;

  score = 0;
  for (n = 0; n < darts; n++) {
    /* generate random numbers for x and y coordinates */
#ifdef _CIVL
    rx = civlrand(n, taskid, curr_round) / (double)RAND_MAX;
    ry = civlrand(n, taskid, curr_round+DARTSB * _mpi_nprocs * ROUNDSB) \
      / (double)RAND_MAX;
#else
    rx = (double)rand()/(double)RAND_MAX;
    ry = (double)rand()/(double)RAND_MAX;
#endif
    x_coord = (2.0 * rx) - 1.0;
    y_coord = (2.0 * ry) - 1.0;

    /* if dart lands in circle, increment score */
    if ((SQR(x_coord) + SQR(y_coord)) <= 1.0)
      score++;
  }
  /* calculate pi */
  pi = 4.0 * (double)score/(double)darts;
  return(pi);
}

/* In CIVL mode, process of rank 0 will do a sequential and store the
   results in "oracle". MPI program will initialize global
   variables */
void initialization() {
#ifdef _CIVL
  double pi = 0.0;
  double avepi = 0.0;

  //$elaborate(DARTS);
  //$elaborate(ROUNDS);
  $assume(N == DARTSB * _mpi_nprocs * ROUNDSB * 2);
  if(taskid == 0) {
    for(curr_round=0; curr_round < ROUNDS; curr_round++) {
      for(int j=0; j < tasks; j++)
        pi += dboard(DARTS, j);
      pi = pi / tasks;
      avepi = ((avepi * curr_round) + pi)/(curr_round + 1); 
      oracle[curr_round] = avepi;
      pi = 0.0;
    }
  }
#else
  DARTS = 100;
  ROUNDS = 500;
#endif
}

int main(int argc, char * argv[]) {
  double homepi;           // local calculated pi
  double avepi = 0;        // average value of pi of all tasks 
                           //and executed rounds
  /* Each value of a round will be used as a message tag to
     communicate among processes at that round */
  int mtype;
  int rc;                  // returned signal of MPI routines

  MPI_Init(&argc, &argv);
  MPI_Comm_size(MPI_COMM_WORLD, &tasks);
  MPI_Comm_rank(MPI_COMM_WORLD, &taskid);
  initialization();
  for(curr_round=0; curr_round<ROUNDS;curr_round++) {
    homepi = dboard(DARTS, taskid);
    if(taskid != MASTER){
      mtype = curr_round;
      rc = MPI_Send(&homepi, 1, MPI_DOUBLE,
                    MASTER, mtype, MPI_COMM_WORLD);
      if (rc != MPI_SUCCESS)
        printf("%d: Send failure on round %d\n", taskid, mtype);
    } else {
      double pi;       // value of pi in a single round 
      double pisum;    // sum of the values of pi calculated by all tasks
      double pirecv;   // MPI receive buffer

      mtype = curr_round;
      pisum = 0;
      for (int n = 1; n < tasks; n++) {
        rc = MPI_Recv(&pirecv, 1, MPI_DOUBLE, MPI_ANY_SOURCE,
                      mtype, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
        if (rc != MPI_SUCCESS) 
          printf("%d: Receive failure on round %d\n", taskid, mtype);
        /* keep running total of pi */
        pisum = pisum + pirecv;
      }
      /* Master calculates the average value of pi for this iteration */
      pi = (pisum + homepi)/tasks;
      /* Master calculates the average value of pi over all iterations */
      avepi = ((avepi * curr_round) + pi)/(curr_round + 1); 
      printf("   After %8d throws, average value of pi = %10.8f\n",
      (DARTS * (curr_round + 1)),avepi);
#ifdef _CIVL
    $assert((avepi == oracle[curr_round]), "avepi is %f but oracle[%d]"
        " is %f\n", avepi, curr_round, oracle[curr_round]);
#endif
    }
  }
  if (taskid == MASTER)
    printf ("\nReal value of PI: 3.1415926535897 \n");
  MPI_Finalize();
  return 0;
}
