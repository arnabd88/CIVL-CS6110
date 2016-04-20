#include<assert.h>

//========================= enums.c ========================
typedef enum color{
  RED,
  BLUE
} color_t;
color_t f()
{
  return RED;
}
int main()
{
  int x = 0;
  int $sef$0 = f();
  if($sef$0 == RED)
  {
    x = 1;
  }
  assert(x == 1);
}
