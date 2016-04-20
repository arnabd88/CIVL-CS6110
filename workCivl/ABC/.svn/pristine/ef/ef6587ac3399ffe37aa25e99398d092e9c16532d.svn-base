      subroutine mxm44_0(A,N1,B,N2,C,N3)
      real a(n1,n2),b(n2,n3),c(n1,n3),s

      do j=1,n3
         do i=1,n1
            c(i,j) = 0.0
            do k=1,n2
               c(i,j) = c(i,j) + a(i,k)*b(k,j)
            enddo
         enddo
      enddo

      return
      end
