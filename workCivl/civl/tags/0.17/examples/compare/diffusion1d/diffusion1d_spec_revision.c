/* FEVS: A Functional Equivalence Verification Suite for High-Performance
 * Scientific Computing
 *
 * Copyright (C) 2009-2010, Stephen F. Siegel, Timothy K. Zirkel,
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


/* diffusion1d_seq.c: sequential version of 1d diffusion.
 * The length of the rod is 1. The endpoints are frozen at the input 
 * temperature.
 *
 */
#include <stdlib.h>
#include <stdio.h>
#include <assert.h>
#include <math.h>
#include <string.h>
#pragma CIVL $input int NX;
#pragma CIVL $input int NXB;
#pragma CIVL $input double K;
#pragma CIVL $input int NSTEPS;
#pragma CIVL $input int NSTEPSB;
#pragma CIVL $input int WSTEP;
#pragma CIVL $output double u_output[NX];
#pragma CIVL $assume 2 < NX && NX <= NXB;
#pragma CIVL $assume 0 < NSTEPS && NSTEPS <= NSTEPSB;

/* Parameters: These are defined at the beginning of the input file:
 *
 *      nx = number of points in x direction, including endpoints
 *       k = D*dt/(dx*dx)
 *  nsteps = number of time steps
 *   wstep = write frame every this many steps
 *
 * Compiling with the flag -DDEBUG will also cause the data to be written
 * to a sequence of plain text files.
 */

/* Global variables */
int nx = -1;              /* number of discrete points including endpoints */
double k = -1;            /* D*dt/(dx*dx) */
int nsteps = -1;          /* number of time steps */
int wstep = -1;           /* write frame every this many time steps */
double *u;                /* temperature function */

void quit(FILE * file) {
  printf("Input file must have format:\n\n");
  printf("nx = <INTEGER>\n");
  printf("k = <DOUBLE>\n");
  printf("nsteps = <INTEGER>\n");
  printf("wstep = <INTEGER>\n");
  printf("<DOUBLE> <DOUBLE> ...\n\n");
  printf("where there are nx doubles at the end.\n");
  fflush(stdout);
  // Missing free(u) and fclose(file) probably is a bug
  free(u);
  fclose(file);
  // Following statements should be added in $exit() or added by CIVL automatically
#pragma CIVL $filesystem_copy_output(CIVL_filesystem, CIVL_output_filesystem);
#pragma CIVL $filesystem_destroy(CIVL_filesystem);
#pragma CIVL $free(stdout);
#pragma CIVL $free(stdin);
#pragma CIVL $free(stderr);
  exit(1);
}

void readint(FILE *file, char *keyword, int *ptr) {
  char buf[101];
  int value;
  int returnval;

  returnval = fscanf(file, "%100s", buf);
  if (returnval != 1) quit(file);
  // fscanf can only make the output argument symbolic, so the 
  // following comparison will always enable 2 transitions.
  // Trivially, for verification of the computing results of sequential program, 
  // we can ignore the transition of executing "quit()". For concurrent programs,
  // ,especially for mpi programs, any one of processes terminated exceptionally
  // will make the some rest processes go into a dead lock (e.g.MPI_Recv forever).
#pragma CIVL $assume strcmp(keyword, buf) == 0;
  if (strcmp(keyword, buf) != 0) quit(file);
  returnval = fscanf(file, "%10s", buf);
  if (returnval != 1) quit(file);
#pragma CIVL $assume strcmp("=", buf) == 0;
  if (strcmp("=", buf) != 0) quit(file);
  returnval = fscanf(file, "%d", ptr);
  if (returnval != 1) quit(file);
}

void readdouble(FILE *file, char *keyword, double *ptr) {
  char buf[101];
  int value;
  int returnval;

  returnval = fscanf(file, "%100s", buf);
  if (returnval != 1) quit(file);
#pragma CIVL $assume strcmp(keyword, buf) == 0;
  if (strcmp(keyword, buf) != 0) quit(file);
  returnval = fscanf(file, "%10s", buf);
  if (returnval != 1) quit(file);
#pragma CIVL $assume strcmp("=", buf) == 0;
  if (strcmp("=", buf) != 0) quit(file);
  returnval = fscanf(file, "%lf", ptr);
  if (returnval != 1) quit(file);
}


/* init: initializes global variables.  read nx, k, nsteps, u, 
 * from infile.  Open GIF output file. */
void init(char* infilename) {
  char keyword[101];
  FILE *infile = fopen(infilename, "r");
  int i;

  assert(infile);
  readint(infile, "nx", &nx);
  readdouble(infile, "k", &k);
  readint(infile, "nsteps", &nsteps);
  readint(infile, "wstep", &wstep);
#pragma CIVL $assume nx == NX;
#pragma CIVL $assume nsteps == NSTEPS;
#pragma CIVL $assume wstep == WSTEP;
#pragma CIVL $assume 0.0 < k && k < 0.5;
  printf("Diffusion1d with nx=%d, k=%f, nsteps=%d, wstep=%d\n",
	 nx, k, nsteps, wstep);
  fflush(stdout);
  assert(nx>=2);
  assert(k>0 && k<.5);
  assert(nsteps >= 1);
  assert(wstep >= 1 && wstep <=nsteps);
  u = (double*)malloc(nx*sizeof(double));
  assert(u);
  for (i = 0; i < nx; i++) {
    if (fscanf(infile, "%lf", u+i) != 1) quit(infile);
  }
  // Missing fclose for FILE * infile
  fclose(infile);
}

/* write_plain: write current data to plain text file and stdout */
/* currently I ignore sprintf stuff and let write_palin only do assignment to ouput
   arguments(which is the only meaningful thing this function does in a verification
   view)*/
void write_plain(int time) {
  for (int i = 0; i < nx; i++)
    u_output[i] = u[i];

  return;
}

/* updates u for next time step. */
void update() {
  int i;
  double u_new[nx];

  for (i = 1; i < nx-1; i++)
    u_new[i] =  u[i] + k*(u[i+1] + u[i-1] -2*u[i]);
  for (i = 1; i < nx-1; i++)
    u[i] = u_new[i];
}

/* main: executes simulation, creates one output file for each time
 * step */
int main(int argc, char *argv[]) {
  int iter;

#pragma CIVL $assume (argc == 2);
  assert(argc==2);
  init(argv[1]);
  write_plain(0);
  for (iter = 1; iter <= nsteps; iter++) {
    update();
    if (iter%wstep==0) write_plain(iter);
  }
  free(u);
  return 0;
}
