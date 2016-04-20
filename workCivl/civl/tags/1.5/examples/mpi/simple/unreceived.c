/* erroneous program: a send is never received.  Will be detected
 * with -deadlock=potential */
#include<mpi.h>

int nprocs;
int myrank;

void main() {
    int argc;
    char **argv;
    double x;
    MPI_Status status;
    
    MPI_Init(&argc, &argv);
    MPI_Comm_rank(MPI_COMM_WORLD, &myrank);
    if (myrank == 0) {
        MPI_Send(&x, 1, MPI_DOUBLE, 0, 1, MPI_COMM_WORLD);
    }
    MPI_Finalize();
}
