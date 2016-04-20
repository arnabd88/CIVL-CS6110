       PROGRAM MXMDRIVER

       INTEGER N
       PARAMETER (N=4)
       real A(N,N),B(N,N),C(N,N)
       INTEGER I,J

       DO J=1,N
         DO I=1,N
           A(I,J) = 1.0*(I+J)
           B(I,J) = 1.0*(I-J)
         ENDDO
       ENDDO

c       DO I=1,N
c         DO J=1,N
c           C(I,J) = 0.0
c           DO K=1,N
c             C(I,J) = C(I,J) + A(I,K)*B(K,J)
c           ENDDO
c         ENDDO
c       ENDDO

       call mxm44_0(A,N,B,N,C,N)

       DO J=1,N
         DO I=1,N
            PRINT *,'C(',I,',',J,') = ',C(I,J)
         ENDDO
       ENDDO

       END 
