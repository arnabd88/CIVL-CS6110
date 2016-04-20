#pragma TASS input int B
#define B 10
#pragma TASS input {n>=0 && n<=B} int n
#define n 10
#pragma TASS input 
double a[n];
#pragma TASS output 
double sum;

void main() {
	double result = 0.0;
	int i;
	
	for (i=0; i<n; i++) result += a[i];
	sum = result;
}
