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


/* 
 * diffusion1d.c: parallel 1d-diffusion simulation.
 */
#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include <assert.h>
#include <math.h>
#include <mpi.h>
#define OWNER(index) ((nprocs*(index+1)-1)/nx)
#pragma CIVL $input int NX;
/* Upper bound for NX */
#pragma CIVL $input int NXB;
#pragma CIVL $input double K;
#pragma CIVL $input int NSTEPS;
/* Upper bound for NSTEPS */
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
// Initialize pointers with NULL so that these 
// pointers can be checked if it's malloced already.
double *u = NULL;         /* temperature function */
double *u_new = NULL;     /* temp. used to update u */

int nprocs;    /* number of processes */
int rank;      /* the rank of this process */
int left;      /* rank of left neighbor */
int right;     /* rank of right neighbor on torus */
int nxl;       /* horizontal extent of one process */
int first;     /* global index for local index 0 */
int start;     /* first local index to update */
int stop;      /* last local index to update */
double *buf;   /* temp. buffer used on proc 0 only */

int firstForProc(int rank) {
  return (rank*nx)/nprocs;	
}

int countForProc(int rank) {
  int a;
  int b;
  
  a = firstForProc(rank+1);
  b = firstForProc(rank);
  return a-b;
}

// Added a argument of File pointer so that file can be closed before the
// program exit.
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
  if(u != NULL)
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

/* init: initializes global variables. */
void init(char* infilename) { 
  char keyword[101];
  FILE *infile = fopen(infilename, "r");
  int i, j;
  
  MPI_Comm_size(MPI_COMM_WORLD, &nprocs);
  MPI_Comm_rank(MPI_COMM_WORLD, &rank);
  if (rank == 0) {
    assert(infile);
    readint(infile, "nx", &nx);
    readdouble(infile, "k", &k);
    readint(infile, "nsteps", &nsteps);
    readint(infile, "wstep", &wstep);
#pragma CIVL $assume nx == NX;
#pragma CIVL $assume nsteps == NSTEPS;
#pragma CIVL $assume wstep == WSTEP;
#pragma CIVL $assume 0.0 < k && k < 0.5;
    printf("Diffusion1d with nx=%d, k=%f, nsteps=%d, wstep=%d nprocs=%d\n",
	   nx, k, nsteps, wstep, nprocs);
  }
  MPI_Bcast(&nx, 1, MPI_INT, 0, MPI_COMM_WORLD);
  MPI_Bcast(&k, 1, MPI_DOUBLE, 0, MPI_COMM_WORLD);
  MPI_Bcast(&nsteps, 1, MPI_INT, 0, MPI_COMM_WORLD);
  MPI_Bcast(&wstep, 1, MPI_INT, 0, MPI_COMM_WORLD);

  assert(k>0 && k<.5);
  assert(nx>=2);
  assert(nsteps>=1);

  // nxl: number actual points (incl. end-points)
  // nxl+2: size of array (incl. ghost cells)
  first = firstForProc(rank);  
  nxl = countForProc(rank);
  if (first == 0 || nxl == 0) left = MPI_PROC_NULL; else left = OWNER(first-1);
  if (first+nxl >= nx || nxl == 0) right = MPI_PROC_NULL; else right = OWNER(first+nxl);  
  
  u = (double*)malloc((nxl+2)*sizeof(double));
  assert(u!=NULL);
  u_new = (double*)malloc((nxl+2)*sizeof(double));
  assert(u_new);
  if (rank == 0) {
    buf = (double*)malloc((1+nx/nprocs)*sizeof(double));
    for (i=1; i <= nxl; i++){
      if (fscanf(infile, "%lf", u+i) != 1) quit(infile);
    }
    for (i=1; i < nprocs; i++){
      for (j=0; j<countForProc(i); j++){
        if (fscanf(infile, "%lf", buf+j) != 1) quit(infile);
      }
      /* Side-effsect removal */
      int count4proc = countForProc(i);
      MPI_Send(buf, count4proc, MPI_DOUBLE, i, 0, MPI_COMM_WORLD);
    }
  }
  else {
    MPI_Recv(u+1, nxl, MPI_DOUBLE, 0, 0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
  }
  if (rank == OWNER(0)) {
    start = 2;
  }
  else {
    start = 1;
  }
  if (rank == OWNER(nx-1)) {
    stop = nxl - 1;
  }
  else {
    stop = nxl;
  }
  if (rank == 0) {
      /* Catch a real bug of this program here :
         Re-malloc on one pointer without free for
         the previous one. */
    free(buf);
    buf = (double*)malloc((1+nx/nprocs)*sizeof(double));
    assert(buf);
  } else {
    buf = NULL;
  }
  // Missing "fclose()" here.
  fclose(infile);
}

// write_plain() is re-written because of not support sprintf() currently.
void write_plain(int time) {
  if (rank != 0) {
    MPI_Send(u+1, nxl, MPI_DOUBLE, 0, 0, MPI_COMM_WORLD);
  } else {
    int source, count, i;
    MPI_Status status;

    for (source = 0; source < nprocs; source++) {
      if (source != 0) {
	MPI_Recv(buf, 1+nx/nprocs, MPI_DOUBLE, source, 0, MPI_COMM_WORLD,
		 &status);
	MPI_Get_count(&status, MPI_DOUBLE, &count);
      } else {
	for (i = 1; i <= nxl; i++) buf[i-1] = u[i];
	count = nxl;
      }
      for (i = 0; i < count; i++) {
	int firstIdx = firstForProc(source);	
#pragma CIVL u_output[firstIdx + i] = buf[i];
      }
    }
  }
}

/* exchange_ghost_cells: updates ghost cells using MPI communication */
void exchange_ghost_cells() {
  MPI_Sendrecv(&u[1], 1, MPI_DOUBLE, left, 0,
	       &u[nxl+1], 1, MPI_DOUBLE, right, 0,
	       MPI_COMM_WORLD, MPI_STATUS_IGNORE);
  MPI_Sendrecv(&u[nxl], 1, MPI_DOUBLE, right, 0,
	       &u[0], 1, MPI_DOUBLE, left, 0,
	       MPI_COMM_WORLD, MPI_STATUS_IGNORE);
}

/* update: updates u.  Uses ghost cells.  Purely local operation. */
void update() {
  int i;

  for (i = start; i <= stop; i++)
    u_new[i] = u[i] + k*(u[i+1] + u[i-1] -2*u[i]);
  for (i = start; i <= stop; i++)
    u[i] = u_new[i];
}

/* main: executes simulation, creates one output file for each time
 * step */
int main(int argc,char *argv[]) {
  int iter;

  MPI_Init(&argc, &argv);
#pragma CIVL $assume (argc == 2);
  assert(argc==2);
  init(argv[1]);
  write_plain(0);
  for (iter = 1; iter <= nsteps; iter++) {
    exchange_ghost_cells();
    update();
    if (iter%wstep==0) write_plain(iter);
  }
  MPI_Finalize();
  free(u);
  free(u_new);
  if (rank == 0) {
    free(buf);
  }

  return 0;
}
