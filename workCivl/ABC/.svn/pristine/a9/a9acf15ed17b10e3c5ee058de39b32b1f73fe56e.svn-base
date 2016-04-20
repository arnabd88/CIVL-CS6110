int f(int* x)
{
  int $sef$0 = *x;
  
  *x = (*x) + 1;
  return $sef$0;
}
int main()
{
  int y = 0;
  
  {
    int i = 0;
    for(; 1; f(&y))
    {
      int $sef$1 = i < 10;
      
      i = i + 1;
      if(!$sef$1)
        break;
      y = 2 * y;
    }
  }
}
