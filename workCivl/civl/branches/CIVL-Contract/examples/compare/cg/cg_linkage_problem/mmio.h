/* 
*   Matrix Market I/O library for ANSI C
*
*   See http://math.nist.gov/MatrixMarket for details.
*
*
*/

#ifndef MM_IO_H
#define MM_IO_H

#define MM_MAX_LINE_LENGTH 1025
#define MatrixMarketBanner "%%MatrixMarket"
#define MM_MAX_TOKEN_LENGTH 64

typedef char MM_typecode[4];

char *mm_typecode_to_str(MM_typecode matcode);

/** @brief reads banner of a file in MM fomat and sets the matcode
 *  @param f filename of file containing the matrix.
 *  @param matcode output matcode of the matrix.
 *  @return 0 on success -1 on failure.
 */
int mm_read_banner(FILE *f, MM_typecode *matcode);
int mm_read_mtx_crd_size(FILE *f, int *M, int *N, int *nz);
int mm_read_mtx_array_size(FILE *f, int *M, int *N);

int mm_write_banner(FILE *f, MM_typecode matcode);
int mm_write_mtx_crd_size(FILE *f, int M, int N, int nz);
int mm_write_mtx_array_size(FILE *f, int M, int N);
/** @brief reads size of RHS matrix in MM format from a file
 *  @param fname filename of file containing the matrix.
 *  @param M_ output #rows.
 *  @param N_ output #columns.
 *  @return 0 on success -1 on failure.
 */
int mm_read_rhs_crd_size(FILE *f, int *M, int *N);
/** @brief reads an RHS  matrix in MM format from a file
 *  @param fname filename of fiel containing the matrix.
 *  @param M_ output #rows.
 *  @param N_ output #columns.
 *  @param val_ output values of MM matrix.
 *  @return 0 on success -1 on failure.
 */
int mm_read_rhs(const char *fname, int *M_, int *N_, double **val_);


/********************* MM_typecode query fucntions ***************************/

#define mm_is_matrix(typecode)	((typecode)[0]=='M')

#define mm_is_sparse(typecode) ( ((typecode)[1]=='C') || ((typecode)[1]=='S') )
#define mm_is_sparserow(typecode)	((typecode)[1]=='S')
//#define mm_is_sparse(typecode)	((typecode)[1]=='C')
#define mm_is_coordinate(typecode)((typecode)[1]=='C')
#define mm_is_dense(typecode)	((typecode)[1]=='A')
#define mm_is_array(typecode)	((typecode)[1]=='A')

#define mm_is_complex(typecode)	((typecode)[2]=='C')
#define mm_is_real(typecode)		((typecode)[2]=='R')
#define mm_is_pattern(typecode)	((typecode)[2]=='P')
#define mm_is_integer(typecode) ((typecode)[2]=='I')

#define mm_is_symmetric(typecode)((typecode)[3]=='S')
#define mm_is_general(typecode)	((typecode)[3]=='G')
#define mm_is_skew(typecode)	((typecode)[3]=='K')
#define mm_is_hermitian(typecode)((typecode)[3]=='H')

int mm_is_valid(MM_typecode matcode);		/* too complex for a macro */


/********************* MM_typecode modify fucntions ***************************/

#define mm_set_matrix(typecode)	((*typecode)[0]='M')
#define mm_set_coordinate(typecode)	((*typecode)[1]='C')
#define mm_set_sparserow(typecode)	((*typecode)[1]='S')
#define mm_set_array(typecode)	((*typecode)[1]='A')
#define mm_set_dense(typecode)	mm_set_array(typecode)
#define mm_set_sparse(typecode)	mm_set_coordinate(typecode)

#define mm_set_complex(typecode)((*typecode)[2]='C')
#define mm_set_real(typecode)	((*typecode)[2]='R')
#define mm_set_pattern(typecode)((*typecode)[2]='P')
#define mm_set_integer(typecode)((*typecode)[2]='I')


#define mm_set_symmetric(typecode)((*typecode)[3]='S')
#define mm_set_general(typecode)((*typecode)[3]='G')
#define mm_set_skew(typecode)	((*typecode)[3]='K')
#define mm_set_hermitian(typecode)((*typecode)[3]='H')

#define mm_clear_typecode(typecode) ((*typecode)[0]=(*typecode)[1]= \
									(*typecode)[2]=' ',(*typecode)[3]='G')

#define mm_initialize_typecode(typecode) mm_clear_typecode(typecode)


/********************* Matrix Market error codes ***************************/


#define MM_COULD_NOT_READ_FILE	11
#define MM_PREMATURE_EOF		12
#define MM_NOT_MTX				13
#define MM_NO_HEADER			14
#define MM_UNSUPPORTED_TYPE		15
#define MM_LINE_TOO_LONG		16
#define MM_COULD_NOT_WRITE_FILE	17


/******************** Matrix Market internal definitions ********************

   MM_matrix_typecode: 4-character sequence

				    ojbect 		sparse/   	data        storage 
						  		dense     	type        scheme

   string position:	 [0]        [1]			[2]         [3]

   Matrix typecode:  M(atrix)  C(oord)		R(eal)   	G(eneral)
						        A(array)	C(omplex)   H(ermitian)
											P(attern)   S(ymmetric)
								    		I(nteger)	K(kew)

 ***********************************************************************/

#define MM_MTX_STR		"matrix"
#define MM_ARRAY_STR	"array"
#define MM_DENSE_STR	"array"
#define MM_COORDINATE_STR "coordinate" 
#define MM_SPARSEROW_STR "sparserow"
#define MM_SPARSE_STR	"coordinate"
#define MM_COMPLEX_STR	"complex"
#define MM_REAL_STR		"real"
#define MM_INT_STR		"integer"
#define MM_GENERAL_STR  "general"
#define MM_SYMM_STR		"symmetric"
#define MM_HERM_STR		"hermitian"
#define MM_SKEW_STR		"skew-symmetric"
#define MM_PATTERN_STR  "pattern"


/*  high level routines */
int mm_write_mtx_crd(char fname[], int M, int N, int nz, int I[], int J[],
		 double val[], MM_typecode matcode);
int mm_read_mtx_crd_data(FILE *f, int M, int N, int nz, int I[], int J[],
		double val[], MM_typecode matcode);
int mm_read_mtx_crd_entry(FILE *f, int *I, int *J, double *real, double *img,
			MM_typecode matcode);

/** @brief reads an unsymmetric sparse matrix in MM format from a file
 *  @param fname filename of fiel containing the matrix.
 *  @param M_ output #rows.
 *  @param N_ output #columns.
 *  @param nz_ output #non zeros.
 *  @param val_ output values of MM matrix.
 *  @param I_ row values of MM matrix.
 *  @param J_ column values of MM matrix.
 *  @return 0 on success -1 on failure.
 */
int mm_read_unsymmetric_sparse(const char *fname, int *M_, int *N_, int *nz_,
                double **val_, int **I_, int **J_);
/** @brief reads an symmetric sparse matrix in MM format from a file
 *  @param fname filename of fiel containing the matrix.
 *  @param M_ output #rows.
 *  @param N_ output #columns.
 *  @param nz_ output #non zeros.
 *  @param val_ output values of MM matrix.
 *  @param I_ output row values of MM matrix.
 *  @param J_ output column values of MM matrix.
 *  @return 0 on success -1 on failure.
 */
int mm_read_symmetric_sparse(const char *fname, int *M_, int *N_, int *nz_,
                double **val_, int **I_, int **J_);

/** @brief reads matrix market format (coordinate) and returns CSR format
 *  @param fn filename of file containing the matrix.
 *  @param m output #rows.
 *  @param n output #columns.
 *  @param nz output #non zeros.
 *  @param i output row values of CSR matrix.
 *  @param j output column values of CSR matrix.
 *  @param a output values of CSR matrix.
 *  @return 0 on success -1 on failure.
 */
int read_mm_matrix (const char *fn, int *m, int *n, int *nz,
                    int **i_idx, int **j_idx, double **a);

/* write CSR format */
/* 1st line : % number_of_rows number_of_columns number_of_nonzeros
 2nd line : % base of index
 3rd line : row_number  nz_r(=number_of_nonzeros_in_the_row)
 next nz_r lines : column_index value(when a != NULL)
 next line : row_number  nz_r(=number_of_nonzeros_in_the_row)
 next nz_r lines : column_index value(when a != NULL)
 ...
 *  @return 0 on success -1 on failure.
 */
int write_csr (const char *fn, int m, int n, int nz,
               int *row_start, int *col_idx, double *a);


/** @brief converts COO format to CSR format, not in-place,
 * if SORT_IN_ROW is defined, each row is sorted in column index
 *  @param n #rows.
 *  @param nz #non zeros.
 *  @param a values of MM matrix.
 *  @param i_idx row values of MM matrix.
 *  @param j_idx column values of MM matrix.
 *  @param csr_a output values of CSR matrix.
 *  @param col_idx output column values of CSR matrix.
 *  @param row_start output row values of CSR matrix.
 *  @return Void.
 */
void coo2csr(int n, int nz, double *a, int *i_idx, int *j_idx,
             double *csr_a, int *col_idx, int *row_start);

#endif
