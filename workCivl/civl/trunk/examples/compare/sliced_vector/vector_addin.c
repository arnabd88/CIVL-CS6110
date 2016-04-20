#include <stdio.h>
#include <stdlib.h>

typedef struct {int * a; int n;} vector;

vector *vector_init(vector * v, int n) {
	v->a = malloc(n*sizeof(int));
	v->n = n;
    for (int i = 0; i < n; ++i) v->a[i] = 0;	
	return v;
}

// program 1:
vector *vector_addin(vector * a, const vector *b){// vector a += b;
	for (int i = 0; i < b->n; ++i)
	   a->a[i] = (a->a[i] + b->a[i])%3; 
	return a;
}

int main(){
    int n = 8;
    vector x; vector_init(&x, n);
    vector y; vector_init(&y, n);
	for (int i = 0; i < x.n; ++i) {	x.a[i] = i%3; y.a[i] = (i/3)%3;		}

	vector_addin(&x, &y);

	int error = 0;
	for (int i = 0; i < x.n; ++i) if (x.a[i] != (i+i/3)%3) error += 1;
	if (error) printf("Unsliced Error\n");
	else printf("Unsliced Good\n");
#ifdef _CIVL
	free(x.a);
	free(y.a);
#endif
	return error ? -1 : 0;
}
