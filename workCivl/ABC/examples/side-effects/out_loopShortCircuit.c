int main()
{
  int i = 0;
  int j = 1;
  while (1)
  {
    int $sef$0;
    if (!(i > (-1)))
      $sef$0 = 0;
    else
    {
      int $sef$5 = i < 10;
      i = i + 1;
      $sef$0 = $sef$5;
    }
    if (!$sef$0)
      break;
    j = i;
  }
  for (; 1; j = j + 1)
  {
    int $sef$1;
    if (!(i > (-1)))
      $sef$1 = 0;
    else
    {
      int $sef$6 = i < 10;
      i = i + 1;
      $sef$1 = $sef$6;
    }
    if (!$sef$1)
      break;
    j = i + j;
  }
  {
    int $sef$4;
    do
    {
      j = i;
      int $sef$2;
      if (!(i > (-1)))
        $sef$2 = 0;
      else
      {
        int $sef$7 = j;
        j = j - 1;
        $sef$2 = $sef$7;
      }
      int $sef$3;
      int $sef$8 = i;
      i = i - 1;
      if ($sef$8)
        $sef$3 = 1;
      else
      {
        int $sef$9 = i < 10;
        i = i + 1;
        $sef$3 = $sef$9;
      }
      $sef$4 = $sef$2 && $sef$3;
    }while ($sef$4);
  }
}
