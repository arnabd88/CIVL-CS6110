      subroutine test(size,array,case)
      integer size, case, i, n
      double precision sum
      double precision array(size)

	
      sum = 0.0d0
      n = 10
      go to (10,30), case
   10 continue
      do 11 i = 1, n, 2
         sum = 1.0d0
   11    continue
      do 12 i = 1, n
         sum = 2.0d0
   12    continue
      go to 50
      
   30 continue
	sum = 0.0d0
      go to 50
      
   50 continue
      return
      
      END
      