/******************************************************************************
 
                          C-DAC Tech Workshop : hyPACK-2013
                             October 15-18,2013 
  Example     : pthread-finding-k-matches.c
  
  Objective   : Finding k matches in the given array
 
  Input       : Number to be search
        Number Of Threads
 
  Output      : Number of times search element found
                Time Taken for finding k matches(in Seconds).                                         
                                                                          
  Created     : MAY-2013   
 
 
  E-mail      : hpcfte@cdac.in       
                                   
****************************************************************************/
 
#include "pthread.h"
#include <stdio.h>
#include <stdlib.h>
#include<sys/time.h>
 
#define ARRAYSIZE   1000
#define MAXTHREADS 8
 
/* global declaration */
double a[ARRAYSIZE];
int count ,num_threads,iterations;
double search_no ;
pthread_mutex_t count_mutex;
 
 
/*Thread callback function*/
void *find_entries(void *tid)
{
        int i, start, *mytid, end;
        int local_count =0;
 
        /* Initialize my part of the global array and keep local count */
        mytid = (int *) tid;
        start = (*mytid * iterations);
        end = start + iterations;
        printf ("Thread %d doing iterations %d to %d\n",*mytid,start,end-1);
        for (i=start; i < end ; i++) {
                if ( a[i] == search_no ) {
                        local_count ++;
                }
        }
 
       /* Lock the mutex and update the global count, then exit */
        pthread_mutex_lock (&count_mutex);
        count = count + local_count;
        pthread_mutex_unlock (&count_mutex);
}
 
/*Main function */
int main(int argc, char *argv[]) {
 
    /*variable declaration */
        int i,start,ret_count;
    int *tids;
        pthread_t * threads;
    pthread_attr_t attr;
        double time_start, time_end;
        struct timeval tv;
        struct timezone tz;
 
        printf("\n\t\t---------------------------------------------------------------------------");
        printf("\n\t\t Centre for Development of Advanced Computing (C-DAC):  February-2008");
        printf("\n\t\t Email : hpcfte@cdac.in");
        printf("\n\t\t---------------------------------------------------------------------------");
        printf("\n\t\t Objective : Finding k matches in the given Array");
        printf("\n\t\t..........................................................................\n");
     
     
    /*initializing Array */
        for (i=0;i<ARRAYSIZE;i++){
                a[i] = (i %10)+1.0;
        }
    if (argc != 3) {
        printf ("Syntax : exec <Number to be search> <Number of thread>\n");
        return 0;
    }
 
        search_no = 50;
        num_threads = 2;
 
    if (num_threads > MAXTHREADS) {
        printf ("Number of thread should be less than or equal to 8\n");
        return 0;
    }
 
    iterations = ARRAYSIZE/num_threads;
 
    threads = (pthread_t *) malloc(sizeof(pthread_t) * num_threads);
    tids = (int *) malloc(sizeof(int) * num_threads);
 
      /*Taking  start time */
         
    gettimeofday(&tv, &tz);
        time_start = (double)tv.tv_sec + (double)tv.tv_usec / 1000000.0;
         
      /* Pthreads setup: initialize mutex and explicitly create threads in a
        joinable state (for portability).  Pass each thread its loop offset */
     
    ret_count = pthread_mutex_init(&count_mutex, NULL);
    if(ret_count)
        {
        printf("\n ERROR : Return code from pthread_mutex_init() is %d ",ret_count);
        exit(-1);
        }
        ret_count=pthread_attr_init(&attr);
        if(ret_count)
        {
        printf("\n ERROR : Return code from pthread_attr_init() is %d ",ret_count);
        exit(-1);
        }
        ret_count = pthread_attr_setdetachstate(&attr, PTHREAD_CREATE_JOINABLE);
       if(ret_count)
       {
        printf("\n ERROR : Return code from pthread_attr_setdetachstate() is %d ",ret_count);
        exit(-1);
       }
 
 
 
        for (i=0; i<num_threads; i++) {
                tids[i] = i;
                ret_count = pthread_create(&threads[i], &attr,find_entries, (void *) &tids[i]);
                if(ret_count)
        {
            printf("\n ERROR : Return code from pthread_create() is %d ",ret_count);
            exit(-1);
            }
         }
 
        /* Wait for all threads to complete then print global count */
        for (i=0; i<num_threads; i++) {
                ret_count = pthread_join(threads[i], NULL);
            if(ret_count)
            {
            printf("\n ERROR : Return code from pthread_join() is %d ",ret_count);
            exit(-1);
            }
         }
     
        /*Taking End time */
         gettimeofday(&tv, &tz);
         time_end = (double)tv.tv_sec + (double)tv.tv_usec / 1000000.0;
 
         
    printf("Number of search element found in list Count= %d\n",count);
    printf("Time in Seconds (T)         :  %lf\n", time_end - time_start);
        /* Clean up and exit */
        ret_count = pthread_attr_destroy(&attr);
        if(ret_count)
        {
        printf("\n ERROR : Return code from pthread_attr_destroy() is %d ",ret_count);
        exit(-1);
        }
        ret_count = pthread_mutex_destroy(&count_mutex);
        if(ret_count)
        {
        printf("\n ERROR : Return code from pthread_mutex_destroy() is %d ",ret_count);
        exit(-1);
        }
	free(threads);
	free(tids);
}
