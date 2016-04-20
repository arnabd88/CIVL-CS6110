/*
Author: Yihao Yan

See challenge 2 of: http://etaps2015.verifythis.org/challenges

-----------------
Problem description:

Various parallel GCD algorithms exist. In this challenge, we consider a
simple Euclid-like algorithm with two parallel threads. One thread
subtracts in one direction, the other thread subtracts in the other
direction, and eventually this procedure converges on GCD.

Verification tasks
------------------

Specify and verify the following behaviour of this parallel GCD algorithm:

Input:  two positive integers a and b
Output: a positive number that is the greatest common divisor of a and b

-----------------
Result:

For any numbers A less than 5 and B less than 7, myGCD returns a common divisor d
of them and the verification shows that there exists no common divisor of A and
B that is greater than d. Therefore, myGCD behaves correctly.

-----------------
command: civl verify parallelGCD.c
*/

#include <civlc.cvh>
#include <stdio.h>

$input int A_BOUND=4;
$input int B_BOUND=6;
$input int A;
$input int B;
$assume (A>0 && B>0 && A<A_BOUND && B<B_BOUND);

int myGCD(int a, int b) {
  $proc proc_a;
  $proc proc_b;

  void worker1() {
    while(a != b){
      if(a>b){
        int t1 = b;
        int t2 = a-t1;
        a = t2;
      }
    }
  }
  void worker2() {
    while(a != b) {
      if(b>a) {
        int t1 = a;
        int t2 = b-t1;
        b = t2;
      }
    }
  }
  proc_a= $spawn worker1();
  proc_b= $spawn worker2();
  $wait(proc_a);
  $wait(proc_b);
  return a;
}

int seqGCD(int a, int b) {
  while(a != b) {
    if(a > b)
      a = a-b;
    if(b > a)
      b = b-a;
  }
  return a;
}

void main() {
  int result1 = myGCD(A, B);
  int minAB = A < B ? A : B;

  $assert($forall {i = (result1+1) .. (minAB)} (A%i != 0 || B%i != 0));
  $assert(A%result1 == 0 && B%result1 == 0);
}
