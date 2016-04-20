/*

An example using MPI_Probe to find the size of a message

The program consists of one sender and one receiver process.
The sender processes draws a randum number and sends a message
of this size to process one. Process one uses MPI_Probe to find
out how large the message is before it is received. It then allocates
a receive-buffer of this size, and receices the message.

Compile the program with 'mpicc -O3 probe.c -o probe'
Run it on 2 processes.

*/

#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <mpi.h>

int main(int argc, char *argv[]) {
  const int tag = 42;	        /* Message tag */
  int   id, ntasks;
  
  MPI_Init(&argc, &argv); /* Initialize MPI */
  MPI_Comm_size(MPI_COMM_WORLD, &ntasks);	/* Get nr of tasks */
  MPI_Comm_rank(MPI_COMM_WORLD, &id);    /* Get id of this process */

  /* Check that we run on two processors */
  if (ntasks != 2) {
    printf("You have to use 2 processes to run this program\n");
    MPI_Finalize();	       /* Quit if there is only one processor */
    exit(0);
  }

  /* Process 0 does this */
  if (id == 0) {
    const int MAX_SIZE = 1000;
    int message_size, i;
    int *numbers;
    float randomnumber;

    /*Pick a random amount of integers to send to process one */
    srandom(time(NULL));   /* Set random seed based on time */
    /* Draw a random number between 0 and 1 */
    randomnumber = (float)random()/(float)RAND_MAX; 
    /* Message size will be between 0 and MAX_SIZE */
    message_size = (int)(randomnumber * MAX_SIZE);
    /* printf("message_size = %d\n", message_size); */

    /* Allocate an array of this size */
    numbers = (int *) malloc(message_size * sizeof(int));
    /* Initialize the message to some numbers */
    for (i=0; i<message_size; i++) {
      numbers[i] = random() % 100;
      /* printf("%d ", numbers[i]); */ /* Print the numbers */
    }
    printf("\n");

    /* Send the array of integers to process one */
    MPI_Send(numbers, message_size, MPI_INT, 1, tag, MPI_COMM_WORLD);
    printf("0 sent %d numbers to process 1\n", message_size);

    /* Process 1 does this */
  } else if (id == 1) {
    MPI_Status status;
    int *message_buf;
    int my_size;
    /* Probe for an incoming message from process zero */
    MPI_Probe(0, tag, MPI_COMM_WORLD, &status);
 
    /* When probe returns, the status object has the size and other
       attributes of the incoming message. Get the size of the message */
    MPI_Get_count(&status, MPI_INT, &my_size);
    printf("Process %d got a message of size %d\n", id, my_size);
 
    /* Allocate a buffer just big enough to store the numbers */
    message_buf = (int*)malloc(sizeof(int) * my_size);
 
    /* Now receive the message into the allocated buffer */
    MPI_Recv(message_buf, my_size, MPI_INT, 0, tag, MPI_COMM_WORLD,
             MPI_STATUS_IGNORE);
    printf("Process %d received %d numbers\n", id, my_size);
    free(message_buf);
  }
  MPI_Finalize();
  exit(0);
}

