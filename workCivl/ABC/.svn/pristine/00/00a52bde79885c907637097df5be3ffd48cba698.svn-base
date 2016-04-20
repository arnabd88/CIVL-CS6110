/* This header file defines the C library time.h */

#ifndef __SYSTIMES__
#define __SYSTIMES__

typedef double clock_t;

struct tms;

#ifndef NULL
#define NULL (void*)0
#endif 

#define CLOCKS_PER_SEC 100

/*
* Calculates the current calendar time and encodes it into time_t format.
*/
clock_t times(struct tms *timer);

#endif
