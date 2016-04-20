/* Sum of an array - Second parallel version */
 
 #include <stdio.h>
 #include <mpi.h>
 
 #define N 100000
 #define MSG_DATA 100
 #define MSG_RESULT 101
 
void master (void);
void slave (void);
 
int main (int argc, char **argv) {
  int myrank;
  MPI_Init (&argc, &argv);
  MPI_Comm_rank (MPI_COMM_WORLD, &myrank);
  if (!myrank)
    master ();
  else
    slave ();
  MPI_Finalize ();
  return 0;
}
 
void master (void) {
  float array[N];
  double mysum, tmpsum;
  unsigned long long step, i;
  int size;
  MPI_Status status;
  //Initialization of the array
  for (i = 0; i < N; i++)
    array[i] = i + 1;
  MPI_Comm_size (MPI_COMM_WORLD, &size);
  if (size != 1)
    step = N / (size - 1);
  //The array is divided by the number of slaves
  for (i = 0; i < size - 1; i++)
    MPI_Send (array + i * step, step, MPI_FLOAT, i + 1, MSG_DATA, MPI_COMM_WORLD);
  //The master completes the work if necessary
  for (i = (size - 1) * step, mysum = 0; i < N; i++)
    mysum += array[i];
  //The master receives the results in any order
  for (i = 1; i < size; mysum += tmpsum, i++)
    MPI_Recv (&tmpsum, 1, MPI_DOUBLE, MPI_ANY_SOURCE, MSG_RESULT, MPI_COMM_WORLD, &status);
  printf ("%lf\n", mysum);
}
 
void slave (void) {
  float array[N];
  double sum;
  unsigned long long i;
  int count;
  MPI_Status status;
  MPI_Recv (array, N, MPI_FLOAT, 0, MSG_DATA, MPI_COMM_WORLD, &status);
  //The slave finds the size of the array
  MPI_Get_count (&status, MPI_FLOAT, &count);
  for (i = 0, sum = 0; i < count; i++)
    sum += array[i];
  MPI_Send (&sum, 1, MPI_DOUBLE, 0, MSG_RESULT, MPI_COMM_WORLD);
}
