#ifdef _CIVL
#include <civlc.cvh>
#endif

/**********************************************************************
 C-DAC Tech Workshop : hyPACK-2013
 Oct 15-18,2013
 
 
 Example 1.3      : mpi-Pthreads-infinity-norm.c
 
 Objective        : Write an MPI-Pthreads program to calculate Infinity
 norm of a matrix using row wise Block-striped
 partitioning.
 
 Pthreads and MPI Library calls are used.
 
 This Example demonstrates the use of:
 
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
 MPI_Reduce
 MPI_Finalize
 
 Input             : The input file holding the matrix.
 
 Output            : Infinity Norm of the given Matrix.
 
 Created           :MAY-2013
 
 E-mail      	   : hpcfte@cdac.in
 
 
 ************************************************************************/

#include <stdio.h>
#include <stdlib.h>
#include <mpi.h>
#include <pthread.h>
#include <math.h>

#ifdef _CIVL
$input int NUM_ROWS_BOUND;
$input int NUM_COLS_BOUND;
#endif

int  MyRank, currentRow, MyNoofRows, NoofCols, GlobalIndex = -1;
int  flag = 0, maxflag = 0, rowlimit;
float **Matrix, *Vector, max;

pthread_mutex_t mutex_Row = PTHREAD_MUTEX_INITIALIZER;
pthread_mutex_t mutex_Flag = PTHREAD_MUTEX_INITIALIZER;
pthread_mutex_t mutex_Max = PTHREAD_MUTEX_INITIALIZER;

/* Routine executed by each thread */

void * MyPartOfCalc(int Id)
{
    
    int    myRow, col;
    float  sum;
    
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
	    #ifdef _CIVL
	    $assume(currentRow < rowlimit);
	    #endif
            if (currentRow >= rowlimit)
            {
                pthread_mutex_unlock(&mutex_Row);
                pthread_exit(0);
            }
            myRow = currentRow;
            currentRow++;
        }
        pthread_mutex_unlock(&mutex_Row);
        
        /*
         * Perform the addition  on the row selected and and store in
         * max if it is the maximum value until now out of computed
         * sums
         */
        
        printf(" Thread Id %d of process with Rank %d operated on Matrix Row %d\n", Id, MyRank, myRow);
        sum = 0.0;
        
        for (col = 0; col < NoofCols; col++)
            sum += fabs(Matrix[myRow][col]);
        
        
        
        pthread_mutex_lock(&mutex_Max);
        
        if (maxflag == 0)
        {
            max = sum;
            maxflag = 1;
        }
        else if (sum > max)
            max = sum;
        
        pthread_mutex_unlock(&mutex_Max);
    }
    
}


//main(int argc, char **argv)
int main(int argc, char **argv)
{
    
    int   iproc, irow, icol, modval, divval, *Displacement;
    int  iprocb, *ArrayNoofRows, Numprocs, Root = 0, NoofRows, VectorSize;
    float  Result;
    
    pthread_t  *threads;
    FILE  *fp;
    
    
    /* MPI Initialisation ... */
    
    MPI_Init(&argc, &argv);
    MPI_Comm_rank(MPI_COMM_WORLD, &MyRank);
    MPI_Comm_size(MPI_COMM_WORLD, &Numprocs);
    
    /* Validity checking for minimum number of processors */
    #ifdef _CIVL
    $assume(Numprocs >= 2);
    #endif
    if (Numprocs < 2)
    {
        printf("Invalid Number of Processors ..... \n");
        printf("Numprocs must be greater than 1 ......\n");
        MPI_Finalize();
        exit(0);
    }
    
    /* Read the Matrix from the file. */
    
    
    fp = fopen("Norm_Data.dat", "r");
    if (!fp)
    {
        printf("\nUnable to open the file Norm_Data.dat");
        exit(0);
    }
    
    fscanf(fp, "%d", &NoofRows);
    fscanf(fp, "%d", &NoofCols);

    #ifdef _CIVL
    $assume(NoofRows <= NUM_ROWS_BOUND);
    $assume(NoofCols <= NUM_COLS_BOUND);
    #endif
    
    printf("\n Rows: %d  Col:%d.", NoofRows, NoofCols);
    
    MPI_Barrier(MPI_COMM_WORLD);
    
    MPI_Bcast(&NoofRows, 1, MPI_INT, Root, MPI_COMM_WORLD);
    MPI_Bcast(&NoofCols, 1, MPI_INT, Root, MPI_COMM_WORLD);
    
    /* Validity checking for negative sizes of Matrix */
    #ifdef _CIVL
    $assume(NoofRows >= 1 && NoofCols >= 1);
    #endif
    if (NoofRows < 1 || NoofCols < 1)
    {
        printf("The number of rows or columns or size of Vector should be atleast one\n");
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
    /* Allocating and Populating the Matrix */
    
    Matrix = (float **) malloc(NoofRows * sizeof(float *));
    for (irow = 0; irow < NoofRows; irow++)
        Matrix[irow] = (float *) malloc(NoofCols * sizeof(float));
    
    for (irow = 0; irow < NoofRows; irow++)
        for (icol = 0; icol < NoofCols; icol++)
            fscanf(fp, "%f", &Matrix[irow][icol]);
    
    
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
    
    MPI_Reduce(&max, &Result, 1, MPI_FLOAT, MPI_MAX, Root, MPI_COMM_WORLD);
    
    
    if (MyRank == Root)
    {
        printf("The matrix is :\n\n");
        for (irow = 0; irow < NoofRows; irow++) 
        {
            for (icol = 0; icol < NoofCols; icol++)
                printf("%.1f ", Matrix[irow][icol]);
            printf("\n");
        }
        printf("The infinity norm is %f \n", Result);
    }
    MPI_Finalize();
    
}
