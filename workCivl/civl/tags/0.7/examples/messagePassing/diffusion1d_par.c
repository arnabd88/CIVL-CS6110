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

#include <stdlib.h>
#include <stdio.h>
#include <assert.h>
#include <math.h>
#include <mpi.h>
#include "gd.h"
#define MAXCOLORS 256
#define OWNER(index) ((nprocs*(index+1)-1)/nx)

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
double *u_new;            /* temp. used to update u */
FILE *file;               /* file containing animated GIF */
gdImagePtr im, previm;    /* pointers to GIF images */
int *colors;              /* colors we will use */

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

void quit() {
  printf("Input file must have format:\n\n");
  printf("nx = <INTEGER>\n");
  printf("k = <DOUBLE>\n");
  printf("nsteps = <INTEGER>\n");
  printf("wstep = <INTEGER>\n");
  printf("<DOUBLE> <DOUBLE> ...\n\n");
  printf("where there are nx doubles at the end.\n");
  fflush(stdout);
  exit(1);
}

void readint(FILE *file, char *keyword, int *ptr) {
  char buf[101];
  int value;
  int returnval;

  returnval = fscanf(file, "%100s", buf);
  if (returnval != 1) quit();
  if (strcmp(keyword, buf) != 0) quit();
  returnval = fscanf(file, "%10s", buf);
  if (returnval != 1) quit();
  if (strcmp("=", buf) != 0) quit();
  returnval = fscanf(file, "%d", ptr);
  if (returnval != 1) quit();
}

void readdouble(FILE *file, char *keyword, double *ptr) {
  char buf[101];
  int value;
  int returnval;

  returnval = fscanf(file, "%100s", buf);
  if (returnval != 1) quit();
  if (strcmp(keyword, buf) != 0) quit();
  returnval = fscanf(file, "%10s", buf);
  if (returnval != 1) quit();
  if (strcmp("=", buf) != 0) quit();
  returnval = fscanf(file, "%lf", ptr);
  if (returnval != 1) quit();
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
    printf("Diffusion1d with nx=%d, k=%f, nsteps=%d, wstep=%d nprocs=%d\n",
	   nx, k, nsteps, wstep, nprocs);
  }
  MPI_Bcast(&nx, 1, MPI_INT, 0, MPI_COMM_WORLD);
  MPI_Bcast(&k, 1, MPI_DOUBLE, 0, MPI_COMM_WORLD);
  MPI_Bcast(&nsteps, 1, MPI_INT, 0, MPI_COMM_WORLD);
  MPI_Bcast(&wstep, 1, MPI_INT, 0, MPI_COMM_WORLD);

  assert(nx>=nprocs); /* is this necessary ? */
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
      if (fscanf(infile, "%lf", u+i) != 1) quit();
    }
    for (i=1; i < nprocs; i++){
      for (j=0; j<countForProc(i); j++){
        if (fscanf(infile, "%lf", buf+j) != 1) quit();
      }
      MPI_Send(buf, countForProc(i), MPI_DOUBLE, i, 0, MPI_COMM_WORLD);
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
    buf = (double*)malloc((1+nx/nprocs)*sizeof(double));
    assert(buf);
    file = fopen("./parout/out.gif", "wb");
    assert(file);
    colors = (int*)malloc(MAXCOLORS*sizeof(int));
    assert(colors);
  } else {
    buf = NULL;
  }
}

void write_plain(int time) {
  if (rank != 0) {
    MPI_Send(u+1, nxl, MPI_DOUBLE, 0, 0, MPI_COMM_WORLD);
  } else {
    int source, i, count;
    char filename[50];
    FILE *plain = NULL;
    MPI_Status status;

    sprintf(filename, "./parout/out_%d", time);
    plain = fopen(filename, "w");
    assert(plain);
    for (source = 0; source < nprocs; source++) {
      if (source != 0) {
	MPI_Recv(buf, 1+nx/nprocs, MPI_DOUBLE, source, 0, MPI_COMM_WORLD,
		 &status);
	MPI_Get_count(&status, MPI_DOUBLE, &count);
      } else {
	for (i = 1; i <= nxl; i++) buf[i-1] = u[i];
	count = nxl;
      }
      for (i = 0; i < count; i++) fprintf(plain, "%8.2f", buf[i]);
    }
    fprintf(plain, "\n");
    fclose(plain);
  }
}

void write_frame(int time) {
  if (rank != 0) {
    MPI_Send(u+1, nxl, MPI_DOUBLE, 0, 0, MPI_COMM_WORLD);
  } else {
    int source, i, j, count, global_index;
    MPI_Status status;

    im = gdImageCreate(nx*PWIDTH,PHEIGHT);
    if (time == 0) {
      for (j=0; j<MAXCOLORS; j++)
	colors[j] = gdImageColorAllocate (im, j, 0, MAXCOLORS-j-1); 
      gdImageGifAnimBegin(im, file, 1, -1);
    } else {
      gdImagePaletteCopy(im, previm);
    }
    global_index = 0;
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

	int color = (int)(buf[i]*MAXCOLORS/M);

	assert(color >= 0);
	if (color >= MAXCOLORS) color = MAXCOLORS-1;
	gdImageFilledRectangle
	  (im, global_index*PWIDTH, 0, (global_index+1)*PWIDTH-1,
	   PHEIGHT-1, colors[color]);
	global_index++;
      }
    }
    if (time == 0) {
      gdImageGifAnimAdd(im, file, 0, 0, 0, 0, gdDisposalNone, NULL);
    } else {
      gdImageGifAnimAdd(im, file, 0, 0, 0, 5, gdDisposalNone, previm);
      gdImageDestroy(previm);
    }
    previm=im;
    im=NULL;
  }
#ifdef DEBUG
  write_plain(time);
#endif
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
  assert(argc==2);
  init(argv[1]);
  write_frame(0);
  for (iter = 1; iter <= nsteps; iter++) {
    exchange_ghost_cells();
    update();
    if (iter%wstep==0) write_frame(iter);
  }
  MPI_Finalize();
  free(u);
  free(u_new);
  if (rank == 0) {
    gdImageDestroy(previm);
    gdImageGifAnimEnd(file);
    fclose(file);
    free(buf);
    free(colors);
  }
  return 0;
}
