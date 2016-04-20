#include <pthread.h>

#define MAXTHRDS 3

pthread_mutex_t mutexsum;
int shared;

void *thread(void *arg)
{
  int local = (int) (arg);
  
  pthread_mutex_lock (&mutexsum);
  shared = local;
  pthread_mutex_unlock (&mutexsum);
}

int main (int argc, char *argv[])
{
  pthread_attr_t attr;
  pthread_t thrds[MAXTHRDS];
  int i;
  
  pthread_mutex_init(&mutexsum, NULL);
  pthread_attr_init(&attr);
  pthread_attr_setdetachstate(&attr, PTHREAD_CREATE_JOINABLE);
  for(i=0;i<MAXTHRDS;i++)
    pthread_create(&thrds[i], &attr, thread, (void *)i);
  for(i=0;i<MAXTHRDS;i++)
    pthread_join(thrds[i], 0);
}
