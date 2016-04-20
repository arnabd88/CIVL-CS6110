#ifndef _QUEUE_TWO_LOCK_
#define _QUEUE_TWO_LOCK_

#include <stdbool.h>
#include <stdlib.h>
#include "queue.h"

typedef int lock_t;
#define FREE 0
#define lock(l) $when (l==0) l=1;
#define unlock(l) l=0;

typedef struct node_t {
  int value;
  struct node_t *next;
} node_t;

struct queue_t {
  node_t *Head;
  node_t *Tail;
  lock_t H_lock;
  lock_t T_lock;
};

void initialize(queue_t *Q) {
  node_t *node = (node_t*)malloc(sizeof(node_t));

  node->next = NULL;            // Make it the only node in the linked list
  Q->Head = Q->Tail = node;     // Both Head and Tail point to it
  Q->H_lock = Q->T_lock = FREE; // Locks are initially free
}
  
void enqueue(queue_t *Q, int value) {
  node_t *node = (node_t*)malloc(sizeof(node_t)); // in root scope
  
  node->value = value;          // Copy enqueued value into node
  node->next = NULL;            // Set next pointer of node to NULL
  lock(Q->T_lock);              // Acquire T_lock in order to access Tail
  Q->Tail->next = node;         // Link node at the end of the linked list
  Q->Tail = node;               // Swing Tail to node
  unlock(Q->T_lock);            // Release T_lock
}
 
_Bool dequeue(queue_t *Q, int *pvalue) {
  node_t *node, *new_head;

  lock(Q->H_lock);              // Acquire H_lock in order to access Head
  node = Q->Head;               // Read Head
  new_head = node->next;        // Read next pointer
  if (new_head == NULL) {       // Is queue empty?
    unlock(Q->H_lock);          // Release H_lock before return
    return false;               // Queue was empty
  }
  *pvalue = new_head->value;    // Queue not empty.  Read value before release
  Q->Head = new_head;           // Swing Head to next node
  unlock(Q->H_lock);            // Release H_lock
  free(node);                   // Free node
  return true;                  // Queue was not empty, dequeue succeeded
}

void freequeue(queue_t q){
  free(q.Head); 
}

#endif
