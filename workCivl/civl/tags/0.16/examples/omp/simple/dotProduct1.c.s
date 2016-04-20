/******************************************************************************
* FILE: omp_reduction.c
* DESCRIPTION:
*   OpenMP Example - Combined Parallel Loop Reduction - C/C++ Version
*   This example demonstrates a sum reduction within a combined parallel loop
*   construct.  Notice that default data element scoping is assumed - there
*   are no clauses specifying shared or private variables.  OpenMP will 
*   automatically make loop index variables private within team threads, and
*   global variables shared.
* AUTHOR: Blaise Barney  5/99
* LAST REVISED: 04/06/05
******************************************************************************/
/**
* This program computes the dot product of two vectors.
* Online source:
* https://computing.llnl.gov/tutorials/openMP/samples/C/omp_reduction.c
**/
#include <omp.h>
#include <stdio.h>
#include <stdlib.h>

int main (int argc, char *argv[]) 
{
int   i, n;
float a[8], b[8], sum;

/* Some initializations */
n = 8;
for (i=0; i < n; i++)
  a[i] = b[i] = i * 1.0;
sum = 0.0;

  for (i=0; i < n; i++){
    sum = sum + (a[i] * b[i]);
    printf("loop %d\n", i);
  }

printf("   Sum = %f\n",sum);

}
