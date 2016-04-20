#ifndef _QUEUE_
#define _QUEUE_

typedef struct queue_t queue_t;

void initialize(queue_t *Q);

void enqueue(queue_t *Q, int value);

_Bool dequeue(queue_t *Q, int *pvalue);

void freequeue(queue_t q);

#endif
