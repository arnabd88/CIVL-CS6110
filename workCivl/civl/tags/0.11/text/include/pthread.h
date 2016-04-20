#ifdef __PTHREAD__
#else
#define __PTHREAD__

#include<pthread-common.h>
#include <civlc.h>

void pthread_cond_init(pthread_cond_t *cond, int kind){
  cond->proccount = 0;
  cond->signal = $false;
}

//Initializes mutex as unlocked and kind as defined by int m
void pthread_mutex_init(pthread_mutex_t *mutex, int m){
  mutex->kind = m;
  mutex->lock = 0;
}

int pthread_mutex_lock(pthread_mutex_t *mutex) {
  $when(mutex->lock == 0) mutex->lock = 1; 
  mutex->owner = $self;
  return 0;
}


int pthread_mutex_unlock(pthread_mutex_t *mutex) {
  mutex->lock = 0; 
  return 0;
}

int pthread_cond_wait(pthread_cond_t *cond, pthread_mutex_t *mutex){
  if(mutex->owner != $self)
  {
    printf("Mutex not owned by thread");
    $assert($false);
    return 0;
  }
  cond->proccount++;
  pthread_mutex_unlock(mutex);
  $when(cond->signal == $true);
  cond->signal = $false;
  --cond->proccount;
  $when(mutex->lock == 0){pthread_mutex_lock(mutex);}
}

int pthread_cond_signal(pthread_cond_t *cond){
  cond->signal = $true;
}

int pthread_cond_broadcast(pthread_cond_t *cond){
  while(cond->proccount > 0){
    cond->signal = $true;
  }
}

int pthread_create(pthread_t *thread, const pthread_attr_t *attr,
		   void *(*start_routine)(void*), void *arg){
  *thread = $spawn start_routine(arg);
  return 0;
}

int pthread_join(pthread_t thread, void **value_ptr) {
  $wait(thread);
  return 0;
}
#endif
