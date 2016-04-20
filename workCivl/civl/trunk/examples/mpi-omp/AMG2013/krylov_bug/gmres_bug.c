#include "krylov_bug.h"
 
void *
hypre_GMRESCreate( hypre_GMRESFunctions *gmres_functions )
{
   hypre_GMRESData *gmres_data;
 
   gmres_data = hypre_CTAllocF(hypre_GMRESData, 1, gmres_functions);
 
   return (void *) gmres_data;
}
