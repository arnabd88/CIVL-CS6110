      PROGRAM TEST
      INTEGER N
      PARAMETER (N=10)
      REAL ARRAY(N) !The index of ARRAY should from 1 to 10.
	ARRAY(11) = 1.0 !It uses an index out of the bound.
      END
      

      