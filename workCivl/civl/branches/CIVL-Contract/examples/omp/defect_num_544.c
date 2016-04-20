/*
 * This program captures VSL ticket #544
 *   https://vsl.cis.udel.edu/trac/civl/ticket/544
 * which reports an error in the OpenMP Simplifier.
 */
#include <omp.h>
#include <stdio.h>
#include <stdlib.h>

#ifdef _CIVL
#define N 4  
#define NEDGES 3
#else
#define N 4
#define NEDGES 3
#endif


void residualPrllel(double uin[N], double resout[N], int edges[NEDGES][2], int colourIA[3]) {
  for(int c=0; c<2; c++) {
    #pragma omp parallel for default(none) shared(edges,uin,resout,colourIA,c)
    for(int e=colourIA[c]; e<colourIA[c+1]; e++) {
      int i = edges[e][0];
      int j = edges[e][1];
      resout[i] = resout[i] + uin[i]*uin[j];
      resout[j] = resout[j] + 2*uin[i]+2*uin[j];
    }
  }
}

void residualPrllel_defect(double uin[N], double resout[N], int edges[NEDGES][2], int colourIA[3]) {
  for(int c=0; c<2; c++) {
    #pragma omp parallel for default(none) shared(edges,uin,resout,colourIA,c)
    for(int e=colourIA[c]; e<colourIA[c+1]; e++) {
      int i = edges[e][0];
      int j = edges[e][1];
      resout[i] += uin[i]*uin[j];
      resout[j] += 2*uin[i]+2*uin[j];
    }
  }
}

int main (int argc, char *argv[]) {
  double input[N];
  double output[N];
  int edges[NEDGES][2];
  int colors[3] = {0, 1, 2};

  for (int i=0; i<N; i++) {
    input[i] = i;
    output[i] = 0;
  }
   
  residualPrllel(input, output, edges, colors);

  for (int i=0; i<N; i++) {
    input[i] = i;
    output[i] = 0;
  }

  residualPrllel_defect(input, output, edges, colors);
}
