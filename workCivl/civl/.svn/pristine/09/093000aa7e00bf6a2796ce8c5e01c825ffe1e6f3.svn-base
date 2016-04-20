/*
Author: Yihao Yan

Download LCP.zip from: http://fm2012.verifythis.org/challenges

-----------------
Problem background:

Together with a suffix array, LCP can be used to solve interesting text
problems, such as finding the longest repeated substring (LRS) in a text.

A suffix array (for a given text) is an array of all suffixes of the
text. For the text [7,8,8,6], the suffix array is
[[7,8,8,6],
   [8,8,6],
     [8,6],
       [6]]

Typically, the suffixes are not stored explicitly as above but
represented as pointers into the original text. The suffixes in a suffix
array  are sorted in lexicographical order. This way, occurrences of
repeated substrings in the original text are neighbors in the suffix
array. 

-----------------
Verification task:

Implement longest repeated substring function and verify that it does so correctly.

-----------------                                                                                                                                                                 
Result:

For all strings with length less than 5, the lrs function returns an index i and a length l.
The verification shows that the sub string with length l starting from index i is repeated in 
the original string and also, there exists no repeated string with length greater than l. Therefore
the implemented function lrs behaves correctly. 

-----------------  
command: minor changes
*/

#include <stdlib.h>
#include <stdio.h>
#include <civlc.cvh>
#include <assert.h>

$input int N_BOUND = 5;
$input int N;
$input int X1[N];
$assume (N < N_BOUND && N >= 0);

int lcp1(int *arr, int n, int x, int y) {
  int l=0;

  while (x+l<n && y+l<n && arr[x+l]==arr[y+l]) {
      l++;
  }
  return l;
}

int compare(int *a, int n, int x, int y) {
    if (x == y) return 0;

    int l = 0;

    while (x+l<n && y+l<n && a[x+l] == a[y+l]) {
        l++;
    }
    if (x+l == n) return -1;
    if (y+l == n) return 1;
    if (a[x+l] < a[y+l]) return -1;
    if (a[x+l] > a[y+l]) return 1;
    return -2;
}

void sort(int *a, int n, int *data) {
    for(int i = 0; i < n + 0; i++) {
        for(int j = i; j > 0 && compare(a, n, data[j - 1], data[j]) > 0; j--) {
            int b = j - 1;
            int t = data[j];

            data[j] = data[b];
            data[b] = t;
        }
    }
}

int lcp2(int *a, int n, int index, int* suffixes) {
    return lcp1(a,n,suffixes[index], suffixes[index-1]);
}

/**
result[0]: index
result[1]: length
*/
void lrs(int* a, int n, int *result) {
  int suffixes[n];

  for(int i=0; i<n; i++) {
    suffixes[i] = i;
  }
  sort(a, n, suffixes);
  for(int i=1; i<n; i++) {
    int len = lcp2(a, n, i,suffixes);

    if(len > result[1]) {
      result[0] = suffixes[i];
      result[1] = len;
    }
  }
}

int main(){
  int* result = (int*)malloc(2* sizeof(int));

  result[0] = 0;
  result[1] = 0;
  lrs(X1, N, result);

  int index = result[0];
  int maxLen = result[1];

  if(N > 1) {
   $assert($exists {int k | k >= 0 && k <= N - maxLen && k != index}(
     $forall {i = 0 .. maxLen-1} X1[k+i] == X1[index+i]
   ));
   $assert(!($exists {int k | k >= 0 && k <= N - maxLen - 1}(
     $exists {int j | j >= 0 && j <= N - maxLen - 1 && j != k}(
       $forall {i = 0 .. maxLen} X1[k+i] == X1[j+i]
   ))));
  }else{
    $assert(index == 0 && maxLen == 0);
  }

  free(result);
  return 0;
}
