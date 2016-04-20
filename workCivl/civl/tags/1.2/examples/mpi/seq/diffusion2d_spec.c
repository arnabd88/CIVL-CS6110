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


/* diffusion2d_seq.c: sequential version of 2d diffusion.
 * The length of the side of the square is 1. Initially entire square
 * is 100 degrees, but edges are held at 0 degrees.
 *
 */
#include <stdlib.h>
#include <stdio.h>
#include <assert.h>
#include <math.h>
#include <string.h>
#include "gd.h"
#define MAXCOLORS 256

/* Constants: the following should be defined at compilation:
 *
 *  NSTEPS = number of time steps
 *   WSTEP = write frame every this many steps
 *      NX = number of points in x direction, including endpoints
 *       K = D*dt/(dx*dx)
 * 
 */

/* Global variables */
int nx = -1;              /* number of discrete points including endpoints */
int ny = -1;			  /* number of rows of points, including endpoints */
double k = -1;            /* D*dt/(dx*dx) */
int nsteps = -1;          /* number of time steps */
int wstep = -1;			  /* write frame every this many time steps */
double dx;                /* distance between two grid points: 1/(nx-1) */
double **u[2];               /* temperature function */
double *u_storage[2];        /* storage for u */
FILE *file;               /* file containing animated GIF */
gdImagePtr im, previm;    /* pointers to consecutive GIF images */
int *colors;              /* colors we will use */

void quit() {
  printf("Input file must have format:\n\n");
  printf("nx = <INTEGER>\n");
  printf("ny = <INTEGER>\n");
  printf("k = <DOUBLE>\n");
  printf("nsteps = <INTEGER>\n");
  printf("wstep = <INTEGER>\n");
  printf("<DOUBLE> <DOUBLE> ...\n\n");
  printf("where there are ny rows of nx doubles at the end.\n");
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
  int i, j, t;
  FILE *infile = fopen(infilename, "r");

  assert(infile);
  readint(infile, "nx", &nx);
  readint(infile, "ny", &ny);
  readdouble(infile, "k", &k);
  readint(infile, "nsteps", &nsteps);
  readint(infile, "wstep", &wstep);
  printf("Diffusion2d with k=%f, nx=%d, ny=%d, nsteps=%d, wstep=%d\n",
	 k, nx, ny, nsteps, wstep);
  fflush(stdout);
  assert(k>0 && k<.5);
  assert(nx>=2);
  assert(ny>=2);
  assert(nsteps>=1);
  assert(wstep >= 1 && wstep <=nsteps);
  dx = 1.0/(nx-1);
  for (t=0; t<2; t++) {
    u_storage[t] = (double*)malloc(nx*ny*sizeof(double));
    assert(u_storage[t]);
    u[t] = (double**)malloc(nx*sizeof(double*));
    assert(u[t]);
    for (i=0; i<nx; i++) {
      u[t][i] = &u_storage[t][i*nx];  
    }
  }

  for (i=0; i < nx; i++){
    for (j=0; j < ny; j++) {
      if (fscanf(infile, "%lf", &u[0][i][j]) != 1) quit();
      u[1][i][j] = u[0][i][j];
	}
  }

  file = fopen("./specout/out.gif", "wb");
  assert(file);
  colors = (int*)malloc(MAXCOLORS*sizeof(int));
  assert(colors);
}

/* write_plain: write current data to plain text file and stdout */
void write_plain(int time) {
  FILE *plain;
  char filename[50];
  char command[50];
  int i,j;
  
  sprintf(filename, "./specout/out_%d", time);
  plain = fopen(filename, "w");
  assert(plain);
  for (i=nx-1; i>=0; i--) {
    for (j=0; j<ny; j++) {
      fprintf(plain, "%8.2f", u[time%2][i][j]);
    }
    fprintf(plain, "\n");
  }
  fprintf(plain, "\n");
  fclose(plain);
  sprintf(command, "cat %s", filename);
  system(command);
}

/* write_frame: add a frame to animation */
void write_frame(int time) {
  int i,j;
  
  im = gdImageCreate(nx*PWIDTH,ny*PWIDTH);
  if (time == 0) {
    for (j=0; j<MAXCOLORS; j++)
      colors[j] = gdImageColorAllocate (im, j, 0, MAXCOLORS-j-1); 
    /* (im, j,j,j); gives gray-scale image */
    gdImageGifAnimBegin(im, file, 1, -1);
  } else {
    gdImagePaletteCopy(im, previm);
  }
  for (i=0; i<nx; i++) {
    for (j=0; j<ny; j++) {
      int color = (int)(u[time%2][i][j]*MAXCOLORS/M);

      assert(color >= 0);
      if (color >= MAXCOLORS) color = MAXCOLORS-1;
      gdImageFilledRectangle(im, j*PWIDTH, i*PWIDTH,
			     (j+1)*PWIDTH-1, (i+1)*PWIDTH-1, colors[color]);
    }
  }
  if (time == 0) {
    gdImageGifAnimAdd(im, file, 0, 0, 0, 0, gdDisposalNone, NULL);
  } else {
    gdImageGifAnimAdd(im, file, 0, 0, 0, 5, gdDisposalNone, previm /*NULL*/);
    gdImageDestroy(previm);
  }
  previm=im;
  im=NULL;
#ifdef DEBUG
  write_plain(time);
#endif
}

/* updates u for next time step. */
void update(int time) {
  int i, j;
  int old = time%2;
  int new = 1-old;

  for (i=1; i<nx-1; i++)
    for (j=1; j<ny-1; j++)
      u[new][i][j] =  u[old][i][j]
	+ k*(u[old][i+1][j] + u[old][i-1][j]
	     + u[old][i][j+1] + u[old][i][j-1] - 4*u[old][i][j]);
}

/* main: executes simulation, creates one output file for each time
 * step */
int main(int argc,char *argv[]) {
  int iter, t;

  assert(argc==2);
  init(argv[1]);
  write_frame(0);
  for (iter = 1; iter <= nsteps; iter++) {
    update(iter);
    if (iter%wstep==0) write_frame(iter);
  }
  gdImageDestroy(previm);
  gdImageGifAnimEnd(file);
  fclose(file);
  free(colors);
  for (t=0; t<2; t++) {
    free(u_storage[t]);
    free(u[t]);
  }
  return 0;
}
