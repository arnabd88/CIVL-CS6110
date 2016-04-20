#include <civlc.h>
#include <pthread.h>

void *foo(void *arg){
  pthread_exit(NULL);
}

int main(void){
  pthread_t p1, p2;
  pthread_create(&p1, NULL, foo, NULL);
  pthread_create(&p2, NULL, foo, NULL);
  pthread_exit(NULL);
}
