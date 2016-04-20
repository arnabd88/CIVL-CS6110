/*BHEADER**********************************************************************
 * Copyright (c) 2008,  Lawrence Livermore National Security, LLC.
 * Produced at the Lawrence Livermore National Laboratory.
 * This file is part of HYPRE.  See file COPYRIGHT for details.
 *
 * HYPRE is free software; you can redistribute it and/or modify it under the
 * terms of the GNU Lesser General Public License (as published by the Free
 * Software Foundation) version 2.1 dated February 1999.
 *
 * $Revision: 2.4 $
 ***********************************************************************EHEADER*/



#include "headers.h"

          
          
int
hypre_BoomerAMGInterpTruncation( hypre_ParCSRMatrix *P,
				 double trunc_factor,        
				 int max_elmts)        
{
   hypre_CSRMatrix *P_diag = hypre_ParCSRMatrixDiag(P);
   int *P_diag_i = hypre_CSRMatrixI(P_diag);
   int *P_diag_j = hypre_CSRMatrixJ(P_diag);
   double *P_diag_data = hypre_CSRMatrixData(P_diag);
   int *P_diag_j_new;
   double *P_diag_data_new;

   hypre_CSRMatrix *P_offd = hypre_ParCSRMatrixOffd(P);
   int *P_offd_i = hypre_CSRMatrixI(P_offd);
   int *P_offd_j = hypre_CSRMatrixJ(P_offd);
   double *P_offd_data = hypre_CSRMatrixData(P_offd);
   int *P_offd_j_new;
   double *P_offd_data_new;

   int n_fine = hypre_CSRMatrixNumRows(P_diag);
   int num_cols = hypre_CSRMatrixNumCols(P_diag);
   int i, j, start_j;
   int ierr = 0;
   double max_coef;
   int next_open = 0;
   int now_checking = 0;
   int next_open_offd = 0;
   int now_checking_offd = 0;
   int num_lost = 0;
   int num_lost_offd = 0;
   int num_lost_global = 0;
   int num_lost_global_offd = 0;
   int P_diag_size;
   int P_offd_size;
   int num_elmts;
   int cnt, cnt_diag, cnt_offd;
   double row_sum;
   double scale;

   /* Threading variables.  Entry i of num_lost_(offd_)per_thread  holds the
    * number of dropped entries over thread i's row range. Cum_lost_per_thread
    * will temporarily store the cumulative number of dropped entries up to 
    * each thread. */
   int my_thread_num, num_threadsID, start, stop;
   int * max_num_threads = hypre_CTAlloc(int, 1);
   int * cum_lost_per_thread;
   int * num_lost_per_thread;
   int * num_lost_offd_per_thread;

   /* Initialize threading variables */
   max_num_threads[0] = hypre_NumThreads();
   cum_lost_per_thread = hypre_CTAlloc(int, max_num_threads[0]);
   num_lost_per_thread = hypre_CTAlloc(int, max_num_threads[0]);
   num_lost_offd_per_thread = hypre_CTAlloc(int, max_num_threads[0]);
   for(i=0; i < max_num_threads[0]; i++)
   {
       num_lost_per_thread[i] = 0;
       num_lost_offd_per_thread[i] = 0;
   }

#ifdef HYPRE_USING_OPENMP
#pragma omp parallel private(i,my_thread_num,num_threadsID,max_coef,j,start_j,row_sum,scale,num_lost,now_checking,next_open,num_lost_offd,now_checking_offd,next_open_offd,start,stop,cnt_diag,cnt_offd,num_elmts,cnt)
#endif
   {
       my_thread_num = hypre_GetThreadNum();
       num_threadsID = hypre_NumActiveThreads();

       /* Compute each thread's range of rows to truncate and compress.  Note,
        * that i, j and data are all compressed as entries are dropped, but
        * that the compression only occurs locally over each thread's row
        * range.  P_diag_i is only made globally consistent at the end of this
        * routine.  During the dropping phases, P_diag_i[stop] will point to
        * the start of the next thread's row range.  */

       /* my row range */
       start = (n_fine/num_threadsID)*my_thread_num;
       if (my_thread_num == num_threadsID-1)
       {  stop = n_fine; }
       else
       {  stop = (n_fine/num_threadsID)*(my_thread_num+1); }

       /* 
        * Truncate based on truncation tolerance 
        */
       

    /*P_diag_i[n_fine] -= num_lost;
    P_offd_i[n_fine] -= num_lost_offd;
   } */
       

#ifdef HYPRE_USING_OPENMP
#pragma omp barrier
#endif

       /* 
        * Synchronize and create new diag data structures 
        */
       if (num_lost_global)
       {


#ifdef HYPRE_USING_OPENMP
#pragma omp barrier
#endif
          /* update P_diag_i with number of dropped entries by all lower ranked
           * threads */
          if(my_thread_num > 0)
          {
              for(i=start; i<stop; i++)
              {
                  P_diag_i[i] -= cum_lost_per_thread[my_thread_num-1];
              }
          }

          if(my_thread_num == 0)
          {

              hypre_TFree(P_diag_j);
              hypre_TFree(P_diag_data);
              hypre_CSRMatrixJ(P_diag) = P_diag_j_new;
              hypre_CSRMatrixData(P_diag) = P_diag_data_new;
              hypre_CSRMatrixNumNonzeros(P_diag) = P_diag_size;
          }
       }


   } /* end parallel region */

   hypre_TFree(max_num_threads);
   hypre_TFree(cum_lost_per_thread);
   hypre_TFree(num_lost_per_thread);
   hypre_TFree(num_lost_offd_per_thread);

   return ierr;
}

void hypre_qsort2abs( int *v,
             double *w,
             int  left,
             int  right )
{
   int i, last;
   if (left >= right)
      return;
   swap2( v, w, left, (left+right)/2);
   last = left;
   for (i = left+1; i <= right; i++)
      if (fabs(w[i]) > fabs(w[left]))
      {
         swap2(v, w, ++last, i);
      }
   swap2(v, w, left, last);
   hypre_qsort2abs(v, w, left, last-1);
   hypre_qsort2abs(v, w, last+1, right);
}
