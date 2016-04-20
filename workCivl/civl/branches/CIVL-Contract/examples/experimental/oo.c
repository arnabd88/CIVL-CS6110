//#include <assert.h>
#include <stdio.h>

typedef struct Point {
  int (*getX)(void);
  int (*getY)(void);
  void (*setX)(int);
  void (*setY)(int);
} Point;

Point make_point(int x0, int y0) {
  int x, y;

  int getX() { return x; }
  int getY() { return y; }
  void setX( int x1 ) { x=x1; }
  void setY( int y1 ) { y=y1; }
  
    x=x0;
    y=y0;
    
  Point result = {&getX, &getY, &setX, &setY};

    
  return result;
}

int main() {
  Point p1 = make_point(0,0);
  Point p2 = make_point(1,2);
  int k = p2.getY();
    
  printf("k=%d\n",k);
    p2.setY(17000);
    k=p2.getY();
    printf("k=%d\n",k);
  //assert(k==0);
}
