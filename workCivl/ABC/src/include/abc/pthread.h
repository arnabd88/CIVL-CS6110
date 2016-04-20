/*
  All specification references correspond to pages in the Standard for Information Technology
Portable Operating System Interface (POSIX)IEEE Computer Society Base Specifications, Issue 7.

Standard modifications to each translation:
header files are altered
errors are changed to assertion violations with appropriate messages
appropriate definitions are changed to input variables
*/

#ifndef __PTHREAD__
#define __PTHREAD__
#ifdef NULL
#else
#define NULL ((void*)0)
#endif
/*#ifdef __SVCOMP__
#else
#include <svcomp.h>
#endif*/

// don't think this should be here, but this is using CIVL's $proc
// need to talk about it...
#include <civlc.cvh>

//Mutex types
enum{
    PTHREAD_MUTEX_NORMAL,
    PTHREAD_MUTEX_RECURSIVE,
    PTHREAD_MUTEX_ERRORCHECK
};

enum{
    PTHREAD_MUTEX_STALLED,
    PTHREAD_MUTEX_ROBUST
};

enum{
    PTHREAD_CREATE_JOINABLE,
    PTHREAD_CREATE_DETACHED
};

enum{
    PTHREAD_SCOPE_SYSTEM,
    PTHREAD_SCOPE_PROCESS
};

enum{
    PTHREAD_INHERIT_SCHED,
    PTHREAD_EXPLICIT_SCHED
};

enum{
    PTHREAD_PROCESS_SHARED,
    PTHREAD_PROCESS_PRIVATE,
};

enum{
    PTHREAD_BARRIER_SERIAL_THREAD
};

//Error definitions
enum{
    EINVAL,      //Designates an invalid value
    ENOTSUP,
    EOWNERDEAD,  //Designates the termination of the owning thread
    EBUSY,        //Mutex is already locked
    EDEADLK,      //If mutex type is errorcheck and already owns the mutex
    EPERM,        //If mutex is robust or errorcheck and does not own the mutex
    ERSCH        
};

typedef struct pthread_mutexattr_t pthread_mutexattr_t;
typedef struct pthread_mutex_t pthread_mutex_t;
typedef struct pthread_barrierattr_t pthread_barrierattr_t;
typedef struct pthread_barrier_t pthread_barrier_t;
typedef struct pthread_spinlock_t pthread_spinlock_t;
typedef struct pthread_attr_t pthread_attr_t;
typedef struct pthread_rwlockattr_t pthread_rwlockattr_t;
typedef struct pthread_rwlock_t pthread_rwlock_t;
typedef struct pthread_cond_t pthread_cond_t;
typedef int pthread_condattr_t;
typedef struct pthread_t pthread_t;

pthread_mutex_t PTHREAD_MUTEX_INITIALIZER;// {0,$proc_null,0,0,{0,0,0,PTHREAD_MUTEX_NORMAL,0}}

// Function Prototypes
int pthread_attr_destroy(pthread_attr_t *);
int pthread_attr_setdetachstate(pthread_attr_t *, int);
int pthread_attr_getdetachstate(const pthread_attr_t *, int *);
int pthread_attr_init(pthread_attr_t *);
int pthread_spin_init(pthread_spinlock_t *, int);
int pthread_spin_destroy(pthread_spinlock_t *);
int pthread_spin_lock(pthread_spinlock_t *);
int pthread_spin_unlock(pthread_spinlock_t *);
int pthread_rwlock_init(pthread_rwlock_t *, const pthread_rwlockattr_t *);
int pthread_rwlock_destroy(pthread_rwlock_t *);
int pthread_rwlock_rdlock(pthread_rwlock_t *);
int pthread_rwlock_wrlock(pthread_rwlock_t *);
int pthread_rwlock_unlock(pthread_rwlock_t *);
int pthread_barrierattr_init(pthread_barrierattr_t *);
int pthread_barrierattr_destroy(pthread_barrierattr_t *);
int pthread_barrier_init(pthread_barrier_t *, const pthread_barrierattr_t *, int);
int pthread_barrier_destroy(pthread_barrier_t *);
int pthread_barrier_wait(pthread_barrier_t *);
int pthread_mutexattr_init(pthread_mutexattr_t *);
int pthread_mutexattr_destroy(pthread_mutexattr_t *);
int pthread_mutexattr_getrobust(const pthread_mutexattr_t *, int *);
int pthread_mutexattr_setrobust(pthread_mutexattr_t *, int);
int pthread_mutexattr_getpshared(const pthread_mutexattr_t *, int *);
int pthread_mutexattr_setpshared(pthread_mutexattr_t *, int);
int pthread_mutexattr_getprotocol(const pthread_mutexattr_t *, int *);
int pthread_mutexattr_setprotocol(pthread_mutexattr_t *, int);
int pthread_mutexattr_gettype(const pthread_mutexattr_t *, int *);
int pthread_mutexattr_settype(pthread_mutexattr_t *, int);
int pthread_mutexattr_getprioceiling(const pthread_mutexattr_t *, int *);
int pthread_mutexattr_setprioceiling(pthread_mutexattr_t *, int);
int pthread_mutex_init(pthread_mutex_t *, const pthread_mutexattr_t *);
int pthread_mutex_destroy(pthread_mutex_t *);
int pthread_cond_init(pthread_cond_t *, void *);
int pthread_cond_destroy(pthread_cond_t *);
int pthread_equal(pthread_t, pthread_t);
int pthread_create(pthread_t *, const pthread_attr_t *, void *(*)(void*), void *);
int pthread_join(pthread_t, void **);
void pthread_exit(void *);
int pthread_mutex_lock(pthread_mutex_t *);
int pthread_mutex_trylock(pthread_mutex_t *);
int pthread_mutex_unlock(pthread_mutex_t *);
int pthread_mutex_consistent(pthread_mutex_t *);
int pthread_cond_wait(pthread_cond_t *, pthread_mutex_t *);
int pthread_cond_signal(pthread_cond_t *);
int pthread_cond_broadcast(pthread_cond_t *);
pthread_t pthread_self(void);


#endif
