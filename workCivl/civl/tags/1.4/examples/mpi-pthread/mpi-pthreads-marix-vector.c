#ifdef _CIVL
#include <civlc.cvh>
#endif

/********************************************************************
 
 C-DAC Tech Workshop : hyPACK-2013
 Oct 15-18,2013
 
 Example 1.4       : mpi-Pthreads-matrix-vector.c
 
 Objective         : To write an MPI-Pthreads program, for computing
 the matrix-vector multiplication using
 Self-Scheduling algorithm. Pthreads and MPI library
 calls are used.
 
 This example demonstrates use of:
 
 pthread_create()
 pthread_join()
 pthread_mutex_lock()
 pthread_mutex_unlock()
 
 MPI_Init
 MPI_Comm_rank
 MPI_Comm_size
 MPI_Barrier
 MPI_Bcast
 MPI_Allgather
 MPI_Gatherv
 MPI_Finalize
 
 Input             : Number of Rows, Columns of the Matrix
 
 Output            : Product of Matrix Vector Multiplication.
 
 Created           :MAY-2013
 
 E-mail      	   : hpcfte@cdac.in
 
 
 **************************************************************************/
#include<stdlib.h>
#include <pthread.h>
#include "mpi.h"
#include <stdio.h>

#ifdef _CIVL
$input int NUM_ROWS_BOUND = 6;
$input int NUM_COLS_BOUND = 6;
#endif

int  MyRank, currentRow, MyNoofRows, NoofCols, GlobalIndex = -1;
float  **Matrix, *Vector, *MyResult;
int  flag = 0, rowlimit;

pthread_mutex_t mutex_Row = PTHREAD_MUTEX_INITIALIZER;
pthread_mutex_t mutex_Flag = PTHREAD_MUTEX_INITIALIZER;

/* Routine executed by each thread */

void * MyPartOfCalc(int Id)
{
    int myRow, icol, myindex;
    
    if (flag == 0)
    {
        pthread_mutex_lock(&mutex_Flag);
        rowlimit = currentRow + MyNoofRows;
        flag++;
        pthread_mutex_unlock(&mutex_Flag);
    }
    while (1)
    {
        
        /*
         * Thread selects the row of Matrix on which it has to do the
         * operation
         */
        
        pthread_mutex_lock(&mutex_Row);
        {
            if (currentRow >= rowlimit)
            {
                pthread_mutex_unlock(&mutex_Row);
                pthread_exit(0);
            }
            myRow = currentRow;
            currentRow++;
            GlobalIndex++;
            myindex = GlobalIndex;
        }
        pthread_mutex_unlock(&mutex_Row);
        
        /*
         * Perform the multiplication on the row selected and store
         * the addendum in MyResult array
         */
        
        printf(" Thread Id %d of process with Rank %d operated on Matrix Row %d\n", Id, MyRank, myRow);
        MyResult[myindex] = 0.0;
        
        for (icol = 0; icol < NoofCols; icol++)
            MyResult[myindex] += Matrix[myRow][icol] * Vector[icol];
    }
    
}


int main(int argc, char **argv)
{
    
    int iproc, irow, icol, modval, divval, *Displacement, iprocb, *ArrayNoofRows;
    int Numprocs, Root = 0, NoofRows, VectorSize;
    float  *Results;
    
    pthread_t      *threads;
    
    
    /* MPI Initialisation ... */
    
    MPI_Init(&argc, &argv);
    MPI_Comm_rank(MPI_COMM_WORLD, &MyRank);
    MPI_Comm_size(MPI_COMM_WORLD, &Numprocs);
    
    /* Validity checking for minimum number of processors */
    
    if (Numprocs < 2)
    {
        printf("Invalid Number of Processors ..... \n");
        printf("Numprocs must be greater than 1 ......\n");
        MPI_Finalize();
        exit(0);
    }
    /* Read the sizes of Matrix and Vector */
    
    if (MyRank == Root)
    {
        printf("Enter the number of rows and columns of Matrix\n");
        scanf("%d %d", &NoofRows, &NoofCols);
        printf("Enter the size of Vector\n");
        scanf("%d", &VectorSize);
        #ifdef _CIVL
        $assume(NoofRows <= NUM_ROWS_BOUND);
        $assume(NoofCols <= NUM_COLS_BOUND);
        #endif
    }
    MPI_Barrier(MPI_COMM_WORLD);
    
    MPI_Bcast(&NoofRows, 1, MPI_INT, Root, MPI_COMM_WORLD);
    MPI_Bcast(&NoofCols, 1, MPI_INT, Root, MPI_COMM_WORLD);
    MPI_Bcast(&VectorSize, 1, MPI_INT, Root, MPI_COMM_WORLD);
    
    /* Validity checking for negative sizes of Matrix and Vector */
    
    #ifdef _CIVL
    $assume(NoofRows >= 1 && NoofCols >= 1 && VectorSize >= 1);
    #endif
    if (NoofRows < 1 || NoofCols < 1 || VectorSize < 1)
    {
        printf("The number of rows,columns or size of Vector should be atleast one\n");
        MPI_Finalize();
        exit(-1);
    }
    /* Validity checking for minimum number of Rows of Matrix */
    
    #ifdef _CIVL
    $assume(NoofRows >= Numprocs);
    #endif
    if (NoofRows < Numprocs)
    {
        printf("The number of rows of Matrix should be greater than number of processors\n");
        MPI_Finalize();
        exit(-1);
    }
    /* Validity checking for suitability of sizes for multiplication */
    #ifdef _CIVL
    $assume(NoofCols == VectorSize);
    #endif
    if (NoofCols != VectorSize)
    {
        printf("The number of columns of Matrix should be equal to size of Vector\n");
        MPI_Finalize();
        exit(-1);
    }
    /* Allocating and Populating the Matrices */
    
    Matrix = (float **) malloc(NoofRows * sizeof(float *));
    for (irow = 0; irow < NoofRows; irow++)
        Matrix[irow] = (float *) malloc(NoofCols * sizeof(float));
    
    //Vector = (float *) malloc(NoofRows * sizeof(float));
    Vector = (float *) malloc(NoofCols * sizeof(float));
    
    for (icol = 0; icol < NoofCols; icol++)
    {
        for (irow = 0; irow < NoofRows; irow++)
            Matrix[irow][icol] = irow + icol;
        Vector[icol] = icol;
    }
    
    
    /* Storing the number of Rows to be operated by each process in array */
    
    modval = NoofRows % Numprocs;
    divval = NoofRows / Numprocs;
    MyNoofRows = (MyRank < modval ? divval + 1 : divval);
    
    ArrayNoofRows = (int *) malloc(Numprocs * sizeof(int));
    MPI_Allgather(&MyNoofRows, 1, MPI_INT, ArrayNoofRows, 1, MPI_INT, MPI_COMM_WORLD);
    
    /* Storing the starting Row to be  operated by each process in array */
    
    Displacement = (int *) malloc(Numprocs * sizeof(int));
    Displacement[0] = 0;
    
    
    for (iproc = 1; iproc < Numprocs; iproc++)
        Displacement[iproc] = Displacement[iproc - 1] + ArrayNoofRows[iproc - 1];
    
    MyResult = (float *) malloc(MyNoofRows * sizeof(float));
    
    currentRow = Displacement[MyRank];
    
    MPI_Barrier(MPI_COMM_WORLD);
    
    /*
     * Call threads equal to number of Rows to be processed by this
     * process
     */
    
    threads = (pthread_t *) malloc(sizeof(pthread_t) * MyNoofRows);
    
    for (irow = 0; irow < MyNoofRows; irow++)
        pthread_create(&threads[irow], NULL, (void *(*) (void *)) MyPartOfCalc, (void *) irow);
    
    MPI_Barrier(MPI_COMM_WORLD);
    for (irow = 0; irow < MyNoofRows; irow++)
        pthread_join(threads[irow], NULL);
    
    MPI_Barrier(MPI_COMM_WORLD);
    
    /* Collection of results from each process using MPI_Gatherv */
    
    Results = (float *) malloc(NoofRows * sizeof(float));
    
    
    MPI_Gatherv(MyResult, MyNoofRows, MPI_FLOAT, Results, ArrayNoofRows, Displacement, MPI_FLOAT, Root, MPI_COMM_WORLD);
    
    /* Printing of the Matrix , Vector and the Result Vector by Root */
    
    if (MyRank == Root)
    {
        printf("\n\nMatrix is\n\n");
        for (irow = 0; irow < NoofRows; irow++)
        {
            printf("Row  %d : ", irow);
            for (icol = 0; icol < NoofCols; icol++)
                printf(" %f ", Matrix[irow][icol]);
            printf("\n");
        }
        printf("\n");
        printf("\n");
        
        printf("Vector is\n\n");
        for (icol = 0; icol < NoofCols; icol++)
            printf("Row  %d : %f \n", icol, Vector[icol]);
        
        printf("\n");
        printf("\n");
        
        printf("\n\nResult Vector is \n\n");
        for (irow = 0; irow < NoofRows; irow++)
            printf("Row  %d : %f \n", irow, Results[irow]);
    }
    printf("\n");
    for (irow = 0; irow < NoofRows; irow++)
      free(Matrix[irow]);
    free(Matrix);
    free(Vector);
    free(ArrayNoofRows);
    free(Displacement);
    free(MyResult);
    free(threads);
    free(Results);
    MPI_Finalize();
    return 0;
}
