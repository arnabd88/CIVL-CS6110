/* This header file defines the C library time.h */

#ifndef __TIME__
#define __TIME__

typedef unsigned long int size_t;

typedef double time_t;

typedef double clock_t;

struct tm;

#ifndef NULL
#define NULL ((void*)0)
#endif 

#define CLOCKS_PER_SEC 100

/*
* Returns a pointer to a string which represents the day and time of the structure timeptr.
*/
char *asctime(const struct tm *timeptr);

/*
* Returns the processor clock time used since the beginning of an implementation-defined era (normally the beginning of the program).
*/
clock_t clock(void);

/* Returns a string representing the localtime based on the argument timer.
 */
char *ctime(const time_t *timer);

/*
Returns the difference of seconds between time1 and time2 (time1-time2).
*/
double difftime(time_t time1, time_t time2);

/*
* The value of timer is broken up into the structure tm and expressed 
* in Coordinated Universal Time (UTC) also known as Greenwich Mean Time (GMT).
*/
struct tm *gmtime(const time_t *timer);

/*
* The value of timer is broken up into the structure tm and expressed in the local time zone.
*/
$system struct tm *localtime(const time_t *timer);

/* Converts the structure pointed to by timeptr into a time_t value according to the local time zone.
 */
time_t mktime(struct tm *timeptr);

/*
* Formats the time represented in the structure timeptr according 
* to the formatting rules defined in format and stored into str.
*/
$system size_t strftime(char *str, size_t maxsize, const char *format, const struct tm *timeptr);

/*
* Calculates the current calender time and encodes it into time_t format.
*/
time_t time(time_t *timer);

#endif
