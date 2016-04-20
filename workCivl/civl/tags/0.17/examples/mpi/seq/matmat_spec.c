/* FEVS: A Functional Equivalence Verification Suite for High-Performance
 * Scientific Computing
 *
 * Copyright (C) 2010, Stephen F. Siegel, Timothy K. Zirkel,
 * University of Delaware
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License as
 * published by the Free Software Foundation; either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA
 * 02110-1301 USA.
 */


#include<stdio.h>
#include<stdlib.h>
#include<assert.h>

int main(int argc, char* argv[]) {
  int i, j, k;
  int L = atoi(argv[1]);
  int M = atoi(argv[2]);
  int N = atoi(argv[3]);
  double A[L][M];
  double B[M][N];
  double C[L][N];
  
  FILE *fp =fopen("data", "r");
  for (i = 0; i < L; i++)
    for (j = 0; j < M; j++)
      fscanf(fp,"%lf", &A[i][j]);
  for (i = 0; i < M; i++)
    for (j = 0; j < N; j++)
      fscanf(fp,"%lf",&B[i][j]);
  for (i = 0; i < L; i++) 
    for (j = 0; j < N; j++) {
      C[i][j] = 0.0;
      for (k = 0; k < M; k++)
	C[i][j] += A[i][k] * B[k][j]; 
    }
  for (i = 0; i < L; i++) {
    for (j = 0; j < N; j++)
      printf("%f ", C[i][j]);
    printf("\n");
  }
  printf("\n");
  fclose(fp);
  return 0;
}
