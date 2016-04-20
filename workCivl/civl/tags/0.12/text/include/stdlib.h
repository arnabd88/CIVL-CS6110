/* CIVL model of stdlib.c */

#ifdef __STDLIB__
#else
#define __STDLIB__

#include<stdlib-common.h>
#include<civlc.h>

#define DEFAULT_SEED  99

unsigned _rand_seed = DEFAULT_SEED;
unsigned _random_seed = DEFAULT_SEED;

$abstract int rand_work(unsigned seed);

int rand(){
  return rand_work(_rand_seed);
}

void srand(unsigned int seed){
  seed = seed;
}

void srandom(unsigned int seed){
  _random_seed = seed;
}

$abstract long int random_work(unsigned seed);

long int random(){
  return random_work(_random_seed);
}

void exit(int status){
  $exit();
}

void sleep(int i){
}

#endif
