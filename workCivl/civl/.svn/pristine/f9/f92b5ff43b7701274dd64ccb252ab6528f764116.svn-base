#include <pthread.h>

int i=1, j=1;

#define NUM 5

void *
t1(void* arg)
{
  int k = 0;

  for (k = 0; k < NUM; k++)
    i+=j;

  pthread_exit(NULL);
}

void *
t2(void* arg)
{
  int k = 0;

  for (k = 0; k < NUM; k++)
    j+=i;

  pthread_exit(NULL);
}

int
main(int argc, char **argv)
{
  pthread_t id1, id2;

  pthread_create(&id1, NULL, t1, NULL);
  pthread_create(&id2, NULL, t2, NULL);
    
  pthread_join(id1, 0);
  pthread_join(id2, 0);

  if (i > 144 || j > 144) {
    ERROR:
    goto ERROR;
  }
  

  return 0;
}
