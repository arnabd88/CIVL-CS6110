      subroutine mxm(A,N1,B,N2,C,N3)
c
      real a(n1,n2),b(n2,n3),c(n1,n3),s

c$OMP PARALLEL DEFAULT(PRIVATE) SHARED(A,B,C,N1,N2,N3)
c$OMP DO
         do j=1,n3
            do i=1,n1
               s = 0.0
               do k=1,n2
                  s = s + a(i,k)*b(k,j)
               enddo
               c(i,j) = s
            enddo
         enddo
c$OMP END DO
c$OMP END PARALLEL

      return
      end
