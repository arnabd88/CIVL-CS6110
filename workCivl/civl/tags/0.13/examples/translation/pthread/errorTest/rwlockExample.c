#include <pthread.h>

#define SIZE 3

pthread_rwlock_t lock;
int glob = 0;
int y = 0;
int * yptr = &y;

void * reader(void * arg){
  pthread_rwlock_rdlock(&lock);
  *yptr = glob;
  pthread_rwlock_unlock(&lock);
}

void * writer(void * arg){
  pthread_rwlock_wrlock(&lock);
  glob++;
  pthread_rwlock_unlock(&lock);
}


int main(){
  pthread_t threads[SIZE];
  pthread_rwlock_init(&lock, NULL);
  for(int x = 0; x < SIZE; x++){
    if(x % 3 == 0){
      pthread_create(&threads[x], NULL, writer, NULL);
    }      
    else{
      pthread_create(&threads[x], NULL, reader, NULL);
    }
  }
  pthread_exit(NULL);
}
