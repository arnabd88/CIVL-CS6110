#include<assert.h>
#include<mpi.h>
#include<civl-mpi.cvh>

$input int in;
$assume(in > 0);
MPI_Comm comm = MPI_COMM_WORLD;

int gimmeOne(int x) 
  $requires {$collective(comm) $mpi_isRecvBufEmpty(0)}
  $requires {$collective(MPI_COMM_WORLD) $true}
  $requires {x > 0}
  $ensures {$collective(MPI_COMM_WORLD) $mpi_isRecvBufEmpty(0)}
  $ensures {$collective(MPI_COMM_WORLD) $result == 1 + x}
  $ensures {x == in}
{
  return 1 + x;
}

int main(int argc, char * argv[]) {
  int x;

  MPI_Init(&argc, &argv);
  x = gimmeOne(in);
  assert(x == 1 + in);
  MPI_Finalize();
}
