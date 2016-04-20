#ifndef _QUEUE_NON_BLOCKING_
#define _QUEUE_NON_BLOCKING_

#include <stdbool.h>
#include <stdlib.h>
#include "queue.h"

typedef struct pointer_t pointer_t;

typedef struct node_t {
  int value;
  pointer_t next;
} node_t;

struct pointer_t {
  node_t* ptr;
  int count;
};

struct queue_t {
  pointer_t Head;
  pointer_t Tail;
};

_Bool eq(pointer_t p1, pointer_t p2){
  return p1.ptr == p2.ptr && p1.count == p2.count;
}

_Bool neq(pointer_t p1, pointer_t p2){
  return p1.ptr != p2.ptr || p1.count != p2.count;
}

_Bool CAS(pointer_t *p, pointer_t old, pointer_t new){
  $atomic{
    if(neq(*p, old))
      return false;
    *p = new;
    return true;
  }
}

void initialize(queue_t *Q){
  node_t *node=(node_t*)malloc(sizeof(node_t)); // Allocate a free node

  node->next.ptr = NULL; // Make it the only node in the linked list
  node->next.count = 0;
  Q->Head.ptr = Q->Tail.ptr = node; // Both Head and Tail point to it
}

void enqueue(queue_t *Q, int value){
  node_t *node = (node_t*) malloc(sizeof(node_t)); // Allocate a new node from the free list
  pointer_t tail, next;
  
  node->value = value; // Copy enqueued value into node
  node->next.ptr = NULL; // Set next pointer of node to NULL
  while(true){ // Keep trying until Enqueue is done
    tail = Q->Tail; // Read Tail.ptr and Tail.count together
    next = tail.ptr->next; // Read next ptr and count fields together
    if(eq(tail, Q->Tail)) // Are tail and next consistent?
      // Was Tail pointing to the last node?
      if(next.ptr == NULL){
	// Try to link node at the end of the linked list
	if(CAS(&tail.ptr->next, next, (pointer_t){node, next.count+1}));
	  break; // Enqueue is done.  Exit loop
      }else{ // Tail was not pointing to the last node
	// Try to swing Tail to the next node
	CAS(&Q->Tail, tail, (pointer_t){next.ptr, tail.count+1});
      }
  }
  // Enqueue is done.  Try to swing Tail to the inserted node
  CAS(&Q->Tail, tail, (pointer_t){node, tail.count+1});
}

_Bool dequeue(queue_t *Q, int *pvalue){
  pointer_t head, tail, next;
    
  while(true){ // Keep trying until Dequeue is done
    head = Q->Head; // Read Head
    tail = Q->Tail; // Read Tail
    next = head.ptr->next; // Read Head.ptr->next
    if(eq(head, Q->Head)) // Are head, tail, and next consistent?
      if(head.ptr == tail.ptr){ // Is queue empty or Tail falling behind?
	if(next.ptr == NULL) // Is queue empty?
	  return false; // Queue is empty, couldn't dequeue
	// Tail is falling behind.  Try to advance it
	CAS(&Q->Tail, tail, (pointer_t){next.ptr, tail.count+1});
      } else{ // No need to deal with Tail
	// Read value before CAS
	// Otherwise, another dequeue might free the next node
	*pvalue = next.ptr->value;
	// Try to swing Head to the next node
	if(CAS(&Q->Head, head, (pointer_t){next.ptr, head.count+1}));
	  break; // Dequeue is done.  Exit loop
      }
  }
  free(head.ptr); // It is safe now to free the old node
  return true; // Queue was not empty, dequeue succeeded
}

void freequeue(queue_t q){
  free(q.Tail.ptr);
}

#endif
