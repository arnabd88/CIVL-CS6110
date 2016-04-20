#ifndef __OMP__
#define __OMP__

typedef struct omp_lock_t omp_lock_t;

typedef struct omp_next_lock_t {
  int id;
} omp_nest_lock_t;

void omp_set_num_threads (int);
int omp_get_num_threads (void);
int omp_get_max_threads (void);
int omp_get_thread_num (void);
int omp_get_num_procs (void);
int omp_in_parallel (void);
void omp_set_dynamic (int);
int omp_get_dynamic (void);
void omp_set_nested (int);
int omp_get_nested (void);
void omp_init_lock (omp_lock_t *);
void omp_destroy_lock (omp_lock_t *);
void omp_set_lock (omp_lock_t *);
void omp_unset_lock (omp_lock_t *);
int omp_test_lock (omp_lock_t *);
void omp_init_nest_lock (omp_nest_lock_t *);
void omp_destroy_nest_lock (omp_nest_lock_t *);
void omp_set_nest_lock (omp_nest_lock_t *);
void omp_unset_nest_lock (omp_nest_lock_t *);
int omp_test_nest_lock (omp_nest_lock_t *);
double omp_get_wtime (void);
double omp_get_wtick (void);

#endif
