#include <pthread.h>
pthread_barrier_t barr;

void * thread_worker(void *arg) {
    // do work
    // now make all the threads sync up
    int id = (int)arg;
    int res = pthread_barrier_wait(&barr);
    pthread_exit(NULL);
}


int main(void) {
    int nthreads = 5;
    pthread_t threads[nthreads];
    pthread_barrier_init(&barr, NULL, nthreads);
    for(int i=0; i<nthreads; i++) {
        pthread_create(&threads[i], NULL, thread_worker, (void *) i);
    }
    for(int i=0; i<nthreads; i++) {
        pthread_join(threads[i], NULL);
    }
    pthread_barrier_destroy(&barr);
    pthread_exit(NULL);
}
