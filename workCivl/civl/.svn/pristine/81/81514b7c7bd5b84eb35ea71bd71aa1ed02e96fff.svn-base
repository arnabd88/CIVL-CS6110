#ifndef _QUEUE_NON_BLOCKING_
#define _QUEUE_NON_BLOCKING_

#include <stdbool.h>
#include <stdlib.h>
#include "queue.h"

typedef struct pointer_t pointer_t;
//typedef struct queue_t queue_t;
typedef struct node_t node_t;
typedef struct freeList freeList;

struct node_t;

struct pointer_t {
  node_t* ptr;
  int count;
};

struct node_t {
  int value;
  pointer_t next;
};

struct queue_t {
  pointer_t Head;
  pointer_t Tail;
};

struct freeList{ 
  node_t *node;
  freeList *next;
};

freeList* list; //declare global list

void initialize(queue_t *Q) {
  node_t *node = (node_t*)malloc(sizeof(node_t));  // Allocate a free node
  
  list=(freeList*)malloc(sizeof(freeList));
  list->node = NULL;								//initialize list
  list->next = NULL;
  node->next.ptr = NULL;                          // Make it the only node in the linked list
  node->next.count = 0;			         // Initialize counter
  Q->Head.ptr = Q->Tail.ptr = node;             // Both Head and Tail point to it
}

void setFree(node_t* freeNode){ //put the node to a special-use free list and not the partner to malloc  
  $atomic{
    freeList *temp = (freeList*)malloc(sizeof(freeList));
   
    temp->node = freeNode;
    temp->next = list->next;
    list->next = temp;
  }
}

void deallocate(freeList *list){ // partner to malloc
  freeList *q;
  
  while(list != NULL){
    q = list->next;
    free(list->node);
    free(list);
    list = q;
  }
}

_Bool equal(pointer_t p1, pointer_t p2){             //define equal() method to compare two pointers 
  return (p1.ptr == p2.ptr) && (p1.count == p2.count);
}

_Bool CAS(pointer_t *dest, pointer_t oldval, pointer_t newval){  //define CAS() method
  $atomic {
    if (equal(*dest, oldval)) {
      *dest = newval;
      return true;
    }
    return false;
  }
}

void enqueue(queue_t *Q, int value) {
  pointer_t tail, next;
  node_t *node = (node_t*)malloc(sizeof(node_t)); // Allocate a new node from the free list

  node->value = value;				// Copy enqueued value into node
  node->next.ptr = NULL;				// Set next pointer of node to NULL

  while (true){					// Keep trying until Enqueue is done
    tail = Q->Tail;				// Read Tail.ptr and Tail.count together
    next = tail.ptr->next;			// Read next ptr and count fields together
    if (equal(tail, Q->Tail))	     // Are tail and next consistent?
      // Was Tail pointing to the last node?
      if (next.ptr == NULL){
	// Try to link node at the end of the linked list
	if (CAS(&tail.ptr->next, next, (pointer_t){ node, next.count + 1 }))
	  break;		// **Enqueue is done.  Exit loop
      }
      else{   // Tail was not pointing to the last node
	// Try to swing Tail to the next node
	CAS(&Q->Tail, tail, (pointer_t){ next.ptr, tail.count + 1 });
      }
  }
  // Enqueue is done.  Try to swing Tail to the inserted node
  CAS(&Q->Tail, tail, (pointer_t){ node, tail.count + 1 });
}

_Bool dequeue(queue_t *Q, int *pvalue) {  //boolean type
  pointer_t head, tail, next;

  while (true){					// Keep trying until Dequeue is done
    head = Q->Head;				// Read Head
    tail = Q->Tail;				// Read Tail
    next = head.ptr->next;			// Read Head.ptr->next
    if (equal(head, Q->Head)) // Are head, tail, and next consistent?
      if (head.ptr == tail.ptr){	        // Is queue empty or Tail falling behind?
	if (next.ptr == NULL)		// Is queue empty?
	  return false;		// Queue is empty, couldn't dequeue
	// Tail is falling behind.  Try to advance it
	CAS(&Q->Tail, tail, (pointer_t){ next.ptr, tail.count + 1 });
      }
      else{
	// Read value before CAS
	// Otherwise, another dequeue might free the next node
	*pvalue = next.ptr->value;
	if (CAS(&Q->Head, head, (pointer_t){ next.ptr, head.count + 1 }))
	  break;// **Dequeue is done.  Exit loop
      }
  }
  setFree(head.ptr);		     // It is safe now to "free" the old node
  return true;                 // Queue was not empty, dequeue succeeded
}

void freequeue(queue_t q){
  deallocate(list);
  free(q.Head.ptr);
}

#endif
