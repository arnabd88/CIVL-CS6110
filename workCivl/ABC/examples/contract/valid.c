/*@ requires \valid(p + 0);
  @ requires \valid(p + (0 .. 5#1));
  @ ensures  \valid(p);
  @*/
void validPointers(int * p) {
  *p = 1;
  return;
}
