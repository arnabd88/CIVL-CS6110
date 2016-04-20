#include <civlc.cvh>
#include <seq.cvh>

typedef struct cqueue_t{
  int data[];
  $proc owner;
} cqueue;

$scope root = $here;

/*@ guards \true;
  @ depends \noact;
  @ assigns \nothing;
  @ reads \nothing;
  @*/
$atomic_f void create(cqueue* q)
{
  q = (cqueue*)$malloc(root, sizeof(cqueue));
  q->owner=$proc_null;
  $seq_init(&q->data, 0, NULL);
}
/*@ depends \read(q->owner);
  @ assigns q->owner;
*/
$atomic_f _Bool lock(cqueue* q)
{
  if(q->owner==$self)
    return $true;
  if(q->owner == $proc_null){
    q->owner=$self;
    return $true;
  }else
    return $false;
}
/*@ pure;
  @ depends \call(enqueue, q, ...), \call(dequeue,q, ...);
  @ reads q->data;
  @ assigns \nothing;
  @*/
$atomic_f int size(cqueue* q)
{
  return $seq_length(&q->data);
}
/*@ reads q->owner;
  @ behavior success:
  @   assumes q->owner==$self;
  @   depends \read(q->owner) + \write(q->owner);
  @   assigns q->owner;
  @ behavior failure:
  @   assumes q->owner!=$self;
  @   depends \noact;
  @   assigns \nothing;
  @*/
$atomic_f _Bool unlock(cqueue* q)
{
  if(q->owner==$self)
  {
    q->owner=$proc_null;
    return $true;
  }
  return $false;
}
/*@ depends \call(enqueue,q, ...), \call(size, q);
  @ assigns q->data;
  @*/
$atomic_f _Bool enqueue(cqueue* q, int v)
{
  $seq_append(&q->data, &v, 1);
}
/*@ depends \call(dequeue, q, ...), \call(size, q);
  @ assigns q->data;
  @*/
$atomic_f _Bool dequeue(cqueue* q, int* res)
{
  $seq_remove(&q->data, $seq_length(&q->data)-1, res, 1);
}

cqueue q;
int a;

void foo(){
  enqueue(&q, 1);
}

void goo(){
  dequeue(&q, &a);
  $assert(a==0);
}

int main(){

  create(&q);
  enqueue(&q, 0);

  $proc p0,p1;

  p0=$spawn foo();
  p1=$spawn goo();
  $wait(p0);
  $wait(p1);
}
