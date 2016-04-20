# 1 "gmres_bug.c"
# 1 "<built-in>" 1
# 1 "<built-in>" 3
# 321 "<built-in>" 3
# 1 "<command line>" 1
# 1 "<built-in>" 2
# 1 "gmres_bug.c" 2
# 1 "./krylov_bug.h" 1




typedef struct
{
   char * (*CAlloc) ( int count, int elt_size );

} hypre_GMRESFunctions;

typedef struct
{
   int k_dim;

} hypre_GMRESData;

void *hypre_GMRESCreate( hypre_GMRESFunctions *gmres_functions );
# 2 "gmres_bug.c" 2

void *
hypre_GMRESCreate( hypre_GMRESFunctions *gmres_functions )
{
   hypre_GMRESData *gmres_data;

   gmres_data = ( (hypre_GMRESData *)(*(gmres_functions->CAlloc))((unsigned int)(1), (unsigned int)sizeof(hypre_GMRESData)) );

   return (void *) gmres_data;
}
