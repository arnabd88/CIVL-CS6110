#ifdef _CIVL
#include <civlc.cvh>
#endif
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

#pragma CIVL $input int NB;
#pragma CIVL $output int __sum;

int main(int argc, char *argv[]) {
  double result = 0.0;
  int n = atoi(argv[1]);
  #pragma CIVL $assume(0 < n && n <= NB);
  int i;
  double a[n];
  FILE *fp = fopen("data","r");

  for (i=0; i<n; i++) fscanf(fp, "%lf", &a[i]);
  for (i=0; i<n; i++) result += a[i];
  printf("%lf",result);
  #pragma CIVL __sum = result;
  fclose(fp);
  return 0;
}
