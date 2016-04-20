// program 2:
#include <stdlib.h>
#include <stdio.h>

typedef struct {int * a; int n;} vector;

vector *vector_init(vector * v, int n) {
	v->a = malloc(n*sizeof(int));
	v->n = n;
    for (int i = 0; i < n; ++i) v->a[i] = 0;	
	return v;
}

//////////////////////////////////////////////////////////////////////
/***
sliced stuff:
 Requires vector size is multiple of 64, and u,v are aligned.
***/

typedef unsigned long int sliced_storage;

typedef struct
{
        sliced_storage b0;
        sliced_storage b1;
} sliced_word;

typedef struct 
{ 
        sliced_word *rep;
        int n_words; //number of words, not number of entries
} sliced_vector;

sliced_word *sliced_word_right_shift(sliced_word *lhs, const int n) {
        lhs->b0 >>= n;
        lhs->b1 >>= n;
        return lhs;
}

sliced_word *sliced_word_addin(sliced_word *lhs, const sliced_word *rhs) {
        sliced_storage a, b, s, t;
        a = lhs->b0 ^ rhs->b1;
        b = lhs->b1 ^ rhs->b0;
        s = a ^ lhs->b1;
        t = b ^ rhs->b1;
        lhs->b1 = a & b;
        lhs->b0 = s | t;
        return lhs;
}

const int *sliced_word_setEntry(sliced_word *lhs, const int i, const int * const x) {
        if ((*x) == 2) {
                lhs->b0 |= (sliced_storage)1 << i;
                lhs->b1 |= (sliced_storage)1 << i;
        }
        else if ((*x) == 1) {
                lhs->b0 |= (sliced_storage)1 << i;
                lhs->b1 &= ~((sliced_storage)1 << i);
        }
        else {
                lhs->b0 &= ~((sliced_storage)1 << i);
                lhs->b1 &= ~((sliced_storage)1 << i);
        }
        return x;
}

int *sliced_word_getEntry(const sliced_word *lhs, int *x, const int i) {
        (*x) = (lhs->b0 & ((sliced_storage)1 << i)) >> i;
        (*x) += (lhs->b1 & ((sliced_storage)1 << i)) >> i;
        return x;
}

sliced_vector *sliced_vector_init(sliced_vector *v, int n) {
        v->n_words = (n + 8*sizeof(sliced_storage) - 1) / (8*sizeof(sliced_storage));
        v->rep = calloc(v->n_words, sizeof(sliced_word));
        return v;
}

// u <- u+v
sliced_vector *sliced_vector_addin(sliced_vector *u, const sliced_vector *v) {
        int i;
        for (i = 0; i < u->n_words; ++i) {
                sliced_word_addin(u->rep + i, v->rep + i);
        }
        return u;
}

// u[i] <-- x
const int *sliced_vector_setEntry(sliced_vector *u, const int i, const int * const x ) {
        int w, o;
        w = i / (8*sizeof(sliced_storage));
        o = i % (8*sizeof(sliced_storage));
        sliced_word_setEntry(u->rep + w, o, x);
        return x;
}


// x <-- u[i]
int *sliced_vector_getEntry(const sliced_vector *const u, int *x, const int i) {
        int w, o;
        w = i / (8*sizeof(sliced_storage));
        o = i % (8*sizeof(sliced_storage));
        sliced_word_getEntry(u->rep + w, x, o);
        return x;
}

sliced_vector* sliced_vector_delete(sliced_vector *u) {
        free(u->rep);
        u->rep = NULL;
        u->n_words = 0;
        return u;
}
//////////////////////////////////////////////////////////////////////

// vector a += b, using conversion to/from sliced form.
vector *vector_addin_using_sliced(vector *a, const vector *b){
    sliced_vector x; sliced_vector_init(&x, a->n);
    sliced_vector y; sliced_vector_init(&y, b->n);
	for (int i = 0; i < a->n; ++i) {	
 		sliced_vector_setEntry(&x, i, &(a->a[i]));
 		sliced_vector_setEntry(&y, i, &(b->a[i]));
	}
	sliced_vector_addin(&x, &y);
	for (int i = 0; i < a->n; ++i) {
		int temp;
		sliced_vector_getEntry(&x, &temp, i);	
		a->a[i] = temp;
    }
}

int main(){
    int n = 128;
    vector x; vector_init(&x, n);
    vector y; vector_init(&y, n);
	for (int i = 0; i < x.n; ++i) {	x.a[i] = i%3; y.a[i] = (i/3)%3;		}

	vector_addin_using_sliced(&x, &y);

	int error = 0;
	for (int i = 0; i < x.n; ++i) if (x.a[i] != (i+i/3)%3) error += 1;
	if (error) printf("Sliced Error\n");
	else printf("Sliced Good\n");
	return error ? -1 : 0;
}
