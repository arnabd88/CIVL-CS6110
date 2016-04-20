//#include<mpi.h>

double * u;
int nx = 10;

/*@
  @ requires \valid(u + (0 .. 10));
  @ requires nx == 10;
  @*/
void update(int x) {
  for (int i = 0; i < nx; i++)
    u[i] = u[i]*2;
}


int main() {
  int dummy = 7;
  update(0);
  dummy=8;
  return 0;
}
