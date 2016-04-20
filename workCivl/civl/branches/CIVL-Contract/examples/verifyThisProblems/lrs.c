/*
Note: This problem has not been solved yet

This is a problem in 2012 as an advance problem for LCP

Here is the description:
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

For the above, example (assuming pointers are 0-based integers), the
sorted suffix array is:

[3,0,2,1]
*/

#include <stdlib.h>
#include <stdio.h>
#include <civlc.cvh>
#include <assert.h>

$input int N=4;
$input int X1[N];

int lcp1(int *arr, int n, int x, int y){
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

int lcp2(int *a, int n, int index, int* suffixes){
    return lcp1(a,n,suffixes[index], suffixes[index-1]);
}

/**
result[0]: index
result[1]: length
*/
void lrs(int* a, int n, int *result){
  int suffixes[n];
  for(int i=0; i<n; i++){
    suffixes[i] = i;
  }
  sort(a, n, suffixes);
  for(int i=1; i<n; i++){
    int len = lcp2(a, n, i,suffixes);
    if(len > result[1]){
      result[0] = suffixes[i];
      result[1] = len;
    }
  }
}

int main(){
  int* result = (int*)malloc(2* sizeof(int));
  result[0] = 0;
  result[1] = 0;
  // int arr[] = {1,2,3,1,2,3};
  lrs(X1, N, result);
  int index = result[0];
  int maxLen = result[1];
   $assert($exists {int k | k >= 0 && k < N - maxLen && k != maxLen}(
     $forall {i = 0 .. maxLen} X1[k+i] == X1[index+i]
   ));

  // printf("index:%d\n", result[0]);
  // printf("length:%d\n", result[1]);
  free(result);
  return 0;
}
