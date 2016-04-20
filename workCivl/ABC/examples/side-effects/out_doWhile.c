//======================== doWhile.c =======================
int f(int i)
{
  return i > 0;
}
int main()
{
  int sum = 0;
  int i = 10;
  {
    int $sef$1;
    do
    {
      int $sef$0 = i;
      i = i - 1;
      sum = sum + $sef$0;
      $sef$1 = f(i);
    }while($sef$1);
  }
  i = 10;
  sum = 0;
  do
  {
    sum = sum + i;
    i = i - 1;
  }while(i);
  i = 10;
  sum = 0;
  {
    int $sef$2;
    do
    {
      sum = sum + i;
      $sef$2 = i;
      i = i - 1;
    }while($sef$2);
  }
}
