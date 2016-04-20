/**
 * This is example 2.27 from ACSL reference 1.9.
 */

int main(){
  int x=0;
  int y = 10;

  /*@ loop invariant 0 <= x && x < 11;
    @*/
  while(y > 0){
    x++;
    y--;
  }
}
