#include <pthread.h>
#include <mpi.h>
#include <stdio.h>

#define TAG 99

$input int _mpi_nprocs = 2;

void * Thread(void * tid) {
  int rank, x, y;

  MPI_Comm_rank(MPI_COMM_WORLD, &rank);
  x = 2*rank + (int)tid;
  for (int j=0; j<2; j++) {
    if (rank == 0) {
     for (int i=0; i<2; i++){
       printf("thread %d of rank %d sends at iteration %d.\n", tid, rank, j);
       MPI_Send(&x, 1, MPI_INT, 1, TAG, MPI_COMM_WORLD);
     }
     for (int i=0; i<2; i++){
       printf("thread %d of rank %d receives at iteration %d.\n", tid, rank, j);
       MPI_Recv(&y, 1, MPI_INT, 1, TAG, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
     }
    } else if (rank == 1) {
      for (int i=0; i<2; i++){
        printf("thread %d of rank %d receives at iteration %d.\n", tid, rank, j);
        MPI_Recv(&y, 1, MPI_INT, 0, TAG, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
      }
      for (int i=0; i<2; i++){
        printf("thread %d of rank %d sends at iteration %d.\n", tid, rank, j);
        MPI_Send(&x, 1, MPI_INT, 0, TAG, MPI_COMM_WORLD);
      }
    }
  }
  pthread_exit(NULL);
}

int main(int argc, char * argv[]) {
  pthread_t threads[2];

  MPI_Init(&argc, &argv);
  for (int i=0; i<2; i++) {
    pthread_create(&threads[i], NULL, Thread, (void *)(long)i);
  }
  for (int i=0; i<2; i++) {
    pthread_join(threads[i], NULL);
  }
  MPI_Finalize();
}
