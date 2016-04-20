#include "queue.h"

void main(){
  queue_t queue;
  int buf;

  initialize(&queue);
  enqueue(&queue, 0);
  dequeue(&queue, &buf);
  freequeue(queue);
}

