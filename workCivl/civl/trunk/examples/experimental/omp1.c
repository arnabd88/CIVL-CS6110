#include <stdio.h>
#include <assert.h>

#ifdef _CIVL
#include <civlc.cvh>
#define n 10
$input double u[n];
#else
#define n 10
#endif

int nEdges = n-1;

void residualPrllel(double uin[n], double resout[n], int edges[nEdges][2], int colourIA[3]) {
  for(int c=0; c<2; c++) {
    #pragma omp parallel for default(none) shared(nEdges,edges,uin,resout,colourIA,c)
    for(int e=colourIA[c]; e<colourIA[c+1]; e++) {
      int i = edges[e][0];
      int j = edges[e][1];
      resout[i] = resout[i] + uin[i]*uin[j];
      resout[j] = resout[j] + 2*uin[i]+2*uin[j];
    }
  }
}

void residualSerial(double uin[n], double resout[n], int edges[nEdges][2]) {
  for(int e=0; e<nEdges; e++) {
    int i = edges[e][0];
    int j = edges[e][1];
    resout[i] = resout[i] + uin[i]*uin[j];
    resout[j] = resout[j] + 2*uin[i]+2*uin[j];
  }
}

int main(int argc, char** argv) {
#ifndef _CIVL
  double u[n];
  for(int i=0; i<n; i++) {
    u[i] = 1;
  }
#endif
  int edgesSerial[nEdges][2];
  for(int i=0; i<nEdges; i++) {
    edgesSerial[i][0] = i;
    edgesSerial[i][1] = i+1;
    printf("serial edge #%d=(%d, %d)\n", i, i, i+1);
  }
  int edgesPrllel[nEdges][2];
  for(int i=0; i<(nEdges+1)/2; i++) {
    edgesPrllel[i][0] = 2*i;
    edgesPrllel[i][1] = 2*i+1;
    printf("parallel edge #%d=(%d, %d) color A\n", i, 2*i, 2*i+1);
  }
  for(int i=1; i<(nEdges+1)/2; i++) {
    edgesPrllel[(nEdges+1)/2+i-1][0] = 2*i-1;
    edgesPrllel[(nEdges+1)/2+i-1][1] = 2*i;
    printf("parallel edge #%d=(%d, %d) color B\n", (nEdges+1)/2+i-1, 2*i-1, 2*i);
  }
  int colourIA[3] = {0, (nEdges+1)/2, nEdges};
  printf("colour markers at %d %d %d\n", colourIA[0], colourIA[1], colourIA[2]);
  double resPrllel[n];
  double resSerial[n];
  for(int i=0; i<n; i++) {
    resSerial[i] = 0;
    resPrllel[i] = 0;
  }
  residualSerial(u, resSerial, edgesSerial);
  residualPrllel(u, resPrllel, edgesPrllel, colourIA);
  for(int i=0; i<n; i++) {
    printf("residual(%d) = %e or %e\n", i, resPrllel[i], resSerial[i]);
    assert(resSerial[i] == resPrllel[i]);
  }
}

