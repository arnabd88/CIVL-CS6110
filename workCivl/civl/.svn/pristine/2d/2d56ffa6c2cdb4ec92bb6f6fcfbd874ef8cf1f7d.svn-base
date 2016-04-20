#include <stdlib.h>
#include <stdbool.h>
#include <assert.h>
#include <time.h>

#ifdef _CIVL
#include <civlc.cvh>
$input int N=10;
$assume (N >= 3);
#else
int N=10;
#endif

/**

NOTE: still need improvement

problem description:
Dancing links is a technique introduced in 1979 by Hitotumatu and
Noshita and later popularized by Knuth. The technique can be used to
efficiently implement a search for all solutions of the exact cover
problem, which in its turn can be used to solve Tiling, Sudoku,
N-Queens, and other problems.

Suppose x points to a node of a doubly linked list; let L[x] and R[x]
point to the predecessor and successor of that node. Then the operations

L[R[x]] := L[x];
R[L[x]] := R[x];

remove x from the list. The subsequent operations

L[R[x]] := x;
R[L[x]] := x;

will put x back into the list again.

command: civl verify -inputN=10 DancingLinks.c

************TODO*************
check the left and right node during iteration

store pointers and compare them

modify to c program

function to check if insert or delete is correct
*/
struct Node{
    struct Node *left;
    struct Node *right;
};

void insert(struct Node *x){
  x->right->left = x;
  x->left->right = x;
}

void delete(struct Node *x){
  x->right->left = x->left;
  x->left->right = x->right;
}

//initilize a linkedlist
struct Node* init(int n){
  struct Node *head = (struct Node *)malloc(sizeof(struct Node));
  struct Node *temp = head;
  temp->left = NULL;
  while(n > 1){
    struct Node *new = (struct Node *)malloc(sizeof(struct Node));
    temp->right = new;
    new->left = temp;
    temp = temp->right;
    n--;
  }
  temp->right = NULL;
  return head;
}

struct Node* getNode(struct Node* list, int index){
  struct Node *result = list;
  while(index >1){
    result = result->right;
    index--;
  }
  return result;
}

void initNodeArray(struct Node** array, struct Node* list, int n){
  struct Node *cur = list;
  int index=0;
  while(n > 0){
    array[index++] = cur;
    cur = cur->right;
    n--;
  }
}

void verifyDelete(struct Node *list, struct Node **nodeArray, int index, int n){
  struct Node *temp1 = list;
  for(int i=0; i<index-1; i++){
    assert(temp1 == nodeArray[i]);
    assert(temp1->left == (nodeArray[i])->left);
    if(i != index-2){
      assert(temp1->right == (nodeArray[i])->right);
    }else{
      if(index == n){
        assert(temp1->right == NULL);
      }else{
        assert(temp1->right == nodeArray[index]);
      }
    }
    temp1 = temp1->right;
  }

  for(int j=index; j<=n-1; j++){
    assert(temp1 == nodeArray[j]);
    assert(temp1->right == (nodeArray[j])->right);
    if(j == index){
      if(index == 1){
        assert(temp1->left == NULL);
      }else{
        assert(temp1->left == nodeArray[index-2]);
      }
    }else{
      assert(temp1->left == (nodeArray[j])->left);
    }
    temp1 = temp1->right;
  }
}

void verifyInsert(struct Node *list, struct Node **nodeArray, int index, int n){
  struct Node *temp1 = list;
  for(int k=0;k < n; k++){
    assert(temp1 == nodeArray[k]);
    assert(temp1->left == (nodeArray[k])->left);
    assert(temp1->right == (nodeArray[k])->right);
    temp1 = temp1->right;
  }
}

int main(){
  // size of the linked list
#ifdef _CIVL
  int n = $choose_int(N-2)+3;
#else
  srand(time(NULL));
  int n = rand()%(N-2)+3;
#endif

  struct Node *list = init(n);
  // the index of the node who get deleted
#ifdef _CIVL
  int index = $choose_int(n-2)+2;
#else
  int index = rand()%(N-2)+2;
#endif

  struct Node *x = getNode(list, index);
  struct Node *nodeArray[n];
  initNodeArray(nodeArray, list, n);

  delete(x);

  verifyDelete(list, nodeArray, index, n);

  insert(x);

  verifyInsert(list, nodeArray, index, n);

  int t = n;
  struct Node *temp1 = list;
  while(t >0){
    struct Node *temp2 = temp1;
    temp1 = temp1->right;
    free(temp2);
    t--;
  }
  return 0;
}
