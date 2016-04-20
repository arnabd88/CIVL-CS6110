#include <pthread.h>

#define N 10
pthread_t threads[N];

void* run(void *arg){
  pthread_exit(NULL);
  return NULL;
}

int main(void){
  for(int i=0; i<N; i++)
    pthread_create(&threads[i], NULL, run, (void*)i);
}
