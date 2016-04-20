#include <civlc.cvh>

/*
Longest Common Prefix (LCP)
Input:  an integer array X1[n], and two indices x and y into this array
Output: length of the longest common prefix of the subarrays of a
        starting at x and y respectively.
*/
$input int N_BOUND=4;
$input int n;
$input int x;
$input int y;
$input int X1[n];

$assume (x < n && y < n && x >=0 && y>=0 && n > 0 && n <= N_BOUND);

int lcp(int *arr, int n, int x, int y){
  int l=0;
  while (x+l<n && y+l<n && arr[x+l]==arr[y+l]) {
      l++;
  }
  return l;
}

void main(){
  int result = lcp(X1, n, x, y);
  $assert($forall {i = 0 .. (result-1)} X1[x+i] == X1[y+i]);
  int maxXY = x > y ? x : y;
  if(result + maxXY < n){
    $assert(X1[x+result] != X1[y+result]);
  }
}
