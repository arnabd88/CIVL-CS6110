//===================== shortCircuit.c =====================
int f(int);
int g(int);
int main()
{
  int i = 0;
  int j = 0;
  {
    int $sef$0;
    if (!(i > 5))
      $sef$0 = 0;
    else
    {
      int $sef$2 = f(i);
      int $sef$3 = $sef$2 < i;
      i = i + 1;
      $sef$0 = $sef$3;
    }
    int $sef$1;
    int $sef$4 = j < 3;
    j = j + 1;
    if ($sef$4)
      $sef$1 = 1;
    else
    {
      int $sef$5 = g(4);
      i = i - 1;
      $sef$1 = $sef$5 > i;
    }
    if (($sef$0 && $sef$1) || (j == 10))
      i = i - j;
  }
}
