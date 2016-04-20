#define hypre_CTAllocF(type, count, funcs) \
( (type *)(*(funcs->CAlloc))\
((unsigned int)(count), (unsigned int)sizeof(type)) )

typedef struct
{
   char * (*CAlloc)        ( int count, int elt_size );

} hypre_GMRESFunctions;

typedef struct
{
   int      k_dim;

} hypre_GMRESData;

void *hypre_GMRESCreate( hypre_GMRESFunctions *gmres_functions );


