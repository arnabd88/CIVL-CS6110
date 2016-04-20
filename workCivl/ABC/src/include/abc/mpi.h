#ifndef __MPI__
#define __MPI__
#include <op.h>
#ifndef NULL
#define NULL ((void*)0)
#endif
#define  MPIX_NO_OP  _NO_OP
#define  MPI_MAX     _MAX 
#define  MPI_MIN     _MIN     
#define  MPI_SUM     _SUM
#define  MPI_PROD    _PROD
#define  MPI_LAND    _LAND   
#define  MPI_BAND    _BAND   
#define  MPI_LOR     _LOR     
#define  MPI_BOR     _BOR     
#define  MPI_LXOR    _LXOR    
#define  MPI_BXOR    _BXOR    
#define  MPI_MINLOC  _MINLOC  
#define  MPI_MAXLOC  _MAXLOC  
#define  MPI_REPLACE _REPLACE

typedef enum Operation MPI_Op;
#define MPI_OP_NULL  (-1)

/* MPI definition */
/* -*- Mode: C; c-basic-offset:4 ; -*- */
/*  
 *  (C) 2001 by Argonne National Laboratory.
 *      See COPYRIGHT in top-level directory.
 */
/* src/include/mpi.h.  Generated from mpi.h.in by configure. */
/* Results of the compare operations. */
#define MPI_IDENT     0
#define MPI_CONGRUENT 1
#define MPI_SIMILAR   2
#define MPI_UNEQUAL   3

#ifdef __MPI_DATATYPE__
#else
#define __MPI_DATATYPE__
typedef enum {
    MPI_CHAR,
    MPI_CHARACTER,
    MPI_SIGNED_CHAR,           
    MPI_UNSIGNED_CHAR,
    MPI_BYTE,           
    MPI_WCHAR,          
    MPI_SHORT,          
    MPI_UNSIGNED_SHORT,
    MPI_INT,            
    MPI_INT16_T,
    MPI_INT32_T,
    MPI_INT64_T,
    MPI_INT8_T,
    MPI_INTEGER,
    MPI_INTEGER1,
    MPI_INTEGER16,
    MPI_INTEGER2,
    MPI_INTEGER4,
    MPI_INTEGER8,
    MPI_UNSIGNED,       
    MPI_LONG,          
    MPI_UNSIGNED_LONG, 
    MPI_FLOAT,          
    MPI_DOUBLE,         
    MPI_LONG_DOUBLE,
    MPI_LONG_LONG_INT,  
    MPI_UNSIGNED_LONG_LONG,
    MPI_LONG_LONG,
    MPI_PACKED,
    MPI_LB,
    MPI_UB,
    MPI_UINT16_T,
    MPI_UINT32_T,
    MPI_UINT64_T,
    MPI_UINT8_T,
    MPI_FLOAT_INT,        
    MPI_DOUBLE_INT,       
    MPI_LONG_INT,         
    MPI_SHORT_INT,        
    MPI_2INT,             
    MPI_LONG_DOUBLE_INT,  
    MPI_AINT,
    MPI_OFFSET,
    MPI_2DOUBLE_PRECISION,
    MPI_2INTEGER,
    MPI_2REAL,
    MPI_C_BOOL,
    MPI_C_COMPLEX,
    MPI_C_DOUBLE_COMPLEX,
    MPI_C_FLOAT_COMPLEX,
    MPI_C_LONG_DOUBLE_COMPLEX,
    MPI_COMPLEX,
    MPI_COMPLEX16,
    MPI_COMPLEX32,
    MPI_COMPLEX4,
    MPI_COMPLEX8,
    MPI_REAL,
    MPI_REAL16,
    MPI_REAL2,
    MPI_REAL4,
    MPI_REAL8
} MPI_Datatype;
#define MPI_DATATYPE_NULL (-1)
#endif

typedef long MPI_Aint;
typedef int MPI_Fint;
typedef struct MPI_Comm MPI_Comm;
typedef struct MPI_Group MPI_Group;
typedef struct MPI_Request * MPI_Request;
typedef struct MPIX_Message MPIX_Message;
typedef struct MPI_File MPI_File;
typedef struct MPI_Errhandler MPI_Errhandler;
typedef struct MPI_User_function MPI_User_function;
typedef struct MPI_Copy_function MPI_Copy_function;
typedef struct MPI_Delete_function MPI_Delete_function;
typedef int MPI_Win;
typedef int MPI_Info;
typedef long long MPI_Offset;

/* for subarray and darray constructors */
#define MPI_ORDER_C              56
#define MPI_ORDER_FORTRAN        57
#define MPI_DISTRIBUTE_BLOCK    121
#define MPI_DISTRIBUTE_CYCLIC   122
#define MPI_DISTRIBUTE_NONE     123
#define MPI_DISTRIBUTE_DFLT_DARG -49767

/* Topology types */
typedef enum MPIR_Topo_type { MPI_GRAPH=1, MPI_CART=2, MPI_DIST_GRAPH=3 } MPIR_Topo_type;

/* for the datatype decoders */
typedef enum MPIR_Combiner_enum {
    MPI_COMBINER_NAMED            = 1,
    MPI_COMBINER_DUP              = 2,
    MPI_COMBINER_CONTIGUOUS       = 3, 
    MPI_COMBINER_VECTOR           = 4,
    MPI_COMBINER_HVECTOR_INTEGER  = 5,
    MPI_COMBINER_HVECTOR          = 6,
    MPI_COMBINER_INDEXED          = 7,
    MPI_COMBINER_HINDEXED_INTEGER = 8, 
    MPI_COMBINER_HINDEXED         = 9, 
    MPI_COMBINER_INDEXED_BLOCK    = 10, 
    MPIX_COMBINER_HINDEXED_BLOCK  = 11,
    MPI_COMBINER_STRUCT_INTEGER   = 12,
    MPI_COMBINER_STRUCT           = 13,
    MPI_COMBINER_SUBARRAY         = 14,
    MPI_COMBINER_DARRAY           = 15,
    MPI_COMBINER_F90_REAL         = 16,
    MPI_COMBINER_F90_COMPLEX      = 17,
    MPI_COMBINER_F90_INTEGER      = 18,
    MPI_COMBINER_RESIZED          = 19
}MPIR_Combiner_enum;

/* C functions */
typedef void (MPI_Handler_function) ( MPI_Comm *, int *, ... );
typedef int (MPI_Comm_copy_attr_function)(MPI_Comm, int, void *, void *, 
					  void *, int *);
typedef int (MPI_Comm_delete_attr_function)(MPI_Comm, int, void *, void *);
typedef int (MPI_Type_copy_attr_function)(MPI_Datatype, int, void *, void *, 
					  void *, int *);
typedef int (MPI_Type_delete_attr_function)(MPI_Datatype, int, void *, void *);
typedef int (MPI_Win_copy_attr_function)(MPI_Win, int, void *, void *, void *,
					 int *);
typedef int (MPI_Win_delete_attr_function)(MPI_Win, int, void *, void *);
/* added in MPI-2.2 */
typedef void (MPI_Comm_errhandler_function)(MPI_Comm *, int *, ...);
typedef void (MPI_File_errhandler_function)(MPI_File *, int *, ...);
typedef void (MPI_Win_errhandler_function)(MPI_Win *, int *, ...);
/* names that were added in MPI-2.0 and deprecated in MPI-2.2 */
typedef MPI_Comm_errhandler_function MPI_Comm_errhandler_fn;
typedef MPI_File_errhandler_function MPI_File_errhandler_fn;
typedef MPI_Win_errhandler_function MPI_Win_errhandler_fn;
/* Function type defs */
typedef int (MPI_Datarep_conversion_function)(void *, MPI_Datatype, int, 
             void *, MPI_Offset, void *);
typedef int (MPI_Datarep_extent_function)(MPI_Datatype datatype, MPI_Aint *,
					  void *);
#define MPI_CONVERSION_FN_NULL ((MPI_Datarep_conversion_function *)0)

#define MPI_NULL_COPY_FN   ((MPI_Copy_function *)0)
#define MPI_NULL_DELETE_FN ((MPI_Delete_function *)0)
#define MPI_COMM_NULL_COPY_FN ((MPI_Comm_copy_attr_function*)0)
#define MPI_COMM_NULL_DELETE_FN ((MPI_Comm_delete_attr_function*)0)
#define MPI_COMM_DUP_FN  ((MPI_Comm_copy_attr_function *)0)
#define MPI_WIN_NULL_COPY_FN ((MPI_Win_copy_attr_function*)0)
#define MPI_WIN_NULL_DELETE_FN ((MPI_Win_delete_attr_function*)0)
#define MPI_WIN_DUP_FN   ((MPI_Win_copy_attr_function*)0)
#define MPI_TYPE_NULL_COPY_FN ((MPI_Type_copy_attr_function*)0)
#define MPI_TYPE_NULL_DELETE_FN ((MPI_Type_delete_attr_function*)0)
#define MPI_TYPE_DUP_FN ((MPI_Type_copy_attr_function*)0)

#define MPI_WIN_NULL ((MPI_Win)0)
/* In addition, there are 5 predefined window attributes that are
   defined for every window */
#define MPI_WIN_BASE           1
#define MPI_WIN_SIZE           3
#define MPI_WIN_DISP_UNIT      5
#define MPIX_WIN_CREATE_FLAVOR 7
#define MPIX_WIN_MODEL         9

/* typeclasses */
#define MPI_TYPECLASS_REAL 1
#define MPI_TYPECLASS_INTEGER 2
#define MPI_TYPECLASS_COMPLEX 3

typedef struct MPI_Status{
  int MPI_SOURCE;
  int MPI_TAG;
  int MPI_ERROR;
  int size;
} MPI_Status;

#define MPI_ANY_SOURCE 	(-1)
#define MPI_ANY_TAG     (-2)
#define MPI_PROC_NULL   (-3)
#define MPI_ROOT        (-4)
#define MPI_REQUEST_NULL    NULL
#define MPI_STATUS_IGNORE   NULL
#define MPI_STATUSES_IGNORE NULL
#define MPI_COMM_NULL       NULL
#define MPI_LOCK_EXCLUSIVE  234
#define MPI_LOCK_SHARED     235

/* Typedefs for generalized requests */
typedef int (MPI_Grequest_cancel_function)(void *, int); 
typedef int (MPI_Grequest_free_function)(void *); 
typedef int (MPI_Grequest_query_function)(void *, MPI_Status *); 

/**************************** Communicators  ************************************/
MPI_Comm MPI_COMM_WORLD;
MPI_Comm MPI_COMM_SELF;
MPI_Comm MPI_COMM_PARENT;
MPI_Comm MPI_COMM_TYPE_SHARED;

/* We require that the C compiler support prototypes */
/* Begin Prototypes */
int MPI_Send(void*, int, MPI_Datatype, int, int, MPI_Comm);
int MPI_Recv(void*, int, MPI_Datatype, int, int, MPI_Comm, MPI_Status *);
int MPI_Get_count( MPI_Status *, MPI_Datatype, int *);
int MPI_Bsend(void*, int, MPI_Datatype, int, int, MPI_Comm);
int MPI_Ssend(void*, int, MPI_Datatype, int, int, MPI_Comm);
int MPI_Rsend(void*, int, MPI_Datatype, int, int, MPI_Comm);
int MPI_Buffer_attach( void*, int);
int MPI_Buffer_detach( void*, int *);
int MPI_Isend(void*, int, MPI_Datatype, int, int, MPI_Comm, MPI_Request *);
int MPI_Ibsend(void*, int, MPI_Datatype, int, int, MPI_Comm, MPI_Request *);
int MPI_Issend(void*, int, MPI_Datatype, int, int, MPI_Comm, MPI_Request *);
int MPI_Irsend(void*, int, MPI_Datatype, int, int, MPI_Comm, MPI_Request *);
int MPI_Irecv(void*, int, MPI_Datatype, int, int, MPI_Comm, MPI_Request *);
int MPI_Wait(MPI_Request *, MPI_Status *);
int MPI_Test(MPI_Request *, int *, MPI_Status *);
int MPI_Request_free(MPI_Request *);
int MPI_Waitany(int, MPI_Request *, int *, MPI_Status *);
int MPI_Testany(int, MPI_Request *, int *, int *, MPI_Status *);
int MPI_Waitall(int, MPI_Request *, MPI_Status *);
int MPI_Testall(int, MPI_Request *, int *, MPI_Status *);
int MPI_Waitsome(int, MPI_Request *, int *, int *, MPI_Status *);
int MPI_Testsome(int, MPI_Request *, int *, int *, MPI_Status *);
int MPI_Iprobe(int, int, MPI_Comm, int *, MPI_Status *);
int MPI_Probe(int, int, MPI_Comm, MPI_Status *);
int MPI_Cancel(MPI_Request *);
int MPI_Test_cancelled(MPI_Status *, int *);
int MPI_Send_init(void*, int, MPI_Datatype, int, int, MPI_Comm, MPI_Request *);
int MPI_Bsend_init(void*, int, MPI_Datatype, int,int, MPI_Comm, MPI_Request *);
int MPI_Ssend_init(void*, int, MPI_Datatype, int,int, MPI_Comm, MPI_Request *);
int MPI_Rsend_init(void*, int, MPI_Datatype, int,int, MPI_Comm, MPI_Request *);
int MPI_Recv_init(void*, int, MPI_Datatype, int,int, MPI_Comm, MPI_Request *);
int MPI_Start(MPI_Request *);
int MPI_Startall(int, MPI_Request *);
int MPI_Sendrecv(void *, int, MPI_Datatype,int, int, void *, int, MPI_Datatype, int, int, MPI_Comm, MPI_Status *);
int MPI_Sendrecv_replace(void*, int, MPI_Datatype, int, int, int, int, MPI_Comm, MPI_Status *);
int MPI_Type_contiguous(int, MPI_Datatype, MPI_Datatype *);
int MPI_Type_vector(int, int, int, MPI_Datatype, MPI_Datatype *);
int MPI_Type_hvector(int, int, MPI_Aint, MPI_Datatype, MPI_Datatype *);
int MPI_Type_indexed(int, int *, int *, MPI_Datatype, MPI_Datatype *);
int MPI_Type_hindexed(int, int *, MPI_Aint *, MPI_Datatype, MPI_Datatype *);
int MPI_Type_struct(int, int *,  MPI_Aint *, MPI_Datatype *, MPI_Datatype *);
int MPI_Address(void*, MPI_Aint *);
int MPI_Type_extent(MPI_Datatype, MPI_Aint *);
int MPI_Type_size(MPI_Datatype, int *);
int MPI_Type_lb(MPI_Datatype, MPI_Aint *);
int MPI_Type_ub(MPI_Datatype, MPI_Aint *);
int MPI_Type_commit(MPI_Datatype *);
int MPI_Type_free(MPI_Datatype *);
int MPI_Get_elements(MPI_Status *, MPI_Datatype, int *);
int MPI_Pack(void*, int, MPI_Datatype, void *, int, int *,  MPI_Comm);
int MPI_Unpack(void*, int, int *, void *, int, MPI_Datatype, MPI_Comm);
int MPI_Pack_size(int, MPI_Datatype, MPI_Comm, int *);
int MPI_Barrier(MPI_Comm );
int MPI_Bcast(void*, int, MPI_Datatype, int, MPI_Comm);
int MPI_Gather(void* , int, MPI_Datatype, void*, int, MPI_Datatype, int, MPI_Comm);
int MPI_Gatherv(void* , int, MPI_Datatype, void*, int *,
                int *, MPI_Datatype, int, MPI_Comm);
int MPI_Scatter(void* , int, MPI_Datatype, void*, int, MPI_Datatype, int, MPI_Comm);
int MPI_Scatterv(void* , int *,int *,  MPI_Datatype, void*, int, MPI_Datatype, int, MPI_Comm);
int MPI_Allgather(void* , int, MPI_Datatype, void*, int, MPI_Datatype, MPI_Comm);
int MPI_Allgatherv(void* , int, MPI_Datatype, void*, int *,
                   int *, MPI_Datatype, MPI_Comm);
int MPI_Alltoall(void* , int, MPI_Datatype, void*, int, MPI_Datatype, MPI_Comm);
int MPI_Alltoallv( void* ,  int *,  int *, MPI_Datatype,
		   void*,  int *,  int *, MPI_Datatype, MPI_Comm);
int MPI_Reduce( void* , void*, int, MPI_Datatype, MPI_Op, int, MPI_Comm);
int MPI_Op_create(MPI_User_function *, int, MPI_Op *);
int MPI_Op_free( MPI_Op *);
int MPI_Allreduce( void*, void*, int, MPI_Datatype, MPI_Op, MPI_Comm);
int MPI_Reduce_scatter(  void* , void*,   int *, MPI_Datatype, MPI_Op, MPI_Comm);
int MPI_Scan(void* , void*, int, MPI_Datatype, MPI_Op, MPI_Comm);
int MPI_Group_size(MPI_Group, int *);
int MPI_Group_rank(MPI_Group, int *);
int MPI_Group_translate_ranks (MPI_Group, int,   int *, MPI_Group, int *);
int MPI_Group_compare(MPI_Group, MPI_Group, int *);
int MPI_Comm_group(MPI_Comm, MPI_Group *);
int MPI_Group_union(MPI_Group, MPI_Group, MPI_Group *);
int MPI_Group_intersection(MPI_Group, MPI_Group, MPI_Group *);
int MPI_Group_difference(MPI_Group, MPI_Group, MPI_Group *);
int MPI_Group_incl(MPI_Group, int,   int *, MPI_Group *);
int MPI_Group_excl(MPI_Group, int,   int *, MPI_Group *);
int MPI_Group_range_incl(MPI_Group, int, int [][3], MPI_Group *);
int MPI_Group_range_excl(MPI_Group, int, int [][3], MPI_Group *);
int MPI_Group_free(MPI_Group *);
int MPI_Comm_size(MPI_Comm, int *);
int MPI_Comm_rank(MPI_Comm, int *);
int MPI_Comm_compare(MPI_Comm, MPI_Comm, int *);
int MPI_Comm_dup(MPI_Comm, MPI_Comm *);
int MPI_Comm_create(MPI_Comm, MPI_Group, MPI_Comm *);
int MPI_Comm_split(MPI_Comm, int, int, MPI_Comm *);
int MPI_Comm_free(MPI_Comm *);
int MPI_Comm_test_inter(MPI_Comm, int *);
int MPI_Comm_remote_size(MPI_Comm, int *);
int MPI_Comm_remote_group(MPI_Comm, MPI_Group *);
int MPI_Intercomm_create(MPI_Comm, int, MPI_Comm, int, int, MPI_Comm * );
int MPI_Intercomm_merge(MPI_Comm, int, MPI_Comm *);
int MPI_Keyval_create(MPI_Copy_function *, MPI_Delete_function *, int *, void*);
int MPI_Keyval_free(int *);
int MPI_Attr_put(MPI_Comm, int, void*);
int MPI_Attr_get(MPI_Comm, int, void *, int *);
int MPI_Attr_delete(MPI_Comm, int);
int MPI_Topo_test(MPI_Comm, int *);
int MPI_Cart_create(MPI_Comm, int,   int *,   int *, int, MPI_Comm *);
int MPI_Dims_create(int, int, int *);
int MPI_Graph_create(MPI_Comm, int,   int *,   int *, int, MPI_Comm *);
int MPI_Graphdims_get(MPI_Comm, int *, int *);
int MPI_Graph_get(MPI_Comm, int, int, int *, int *);
int MPI_Cartdim_get(MPI_Comm, int *);
int MPI_Cart_get(MPI_Comm, int, int *, int *, int *);
int MPI_Cart_rank(MPI_Comm, int *, int *);
int MPI_Cart_coords(MPI_Comm, int, int, int *);
int MPI_Graph_neighbors_count(MPI_Comm, int, int *);
int MPI_Graph_neighbors(MPI_Comm, int, int, int *);
int MPI_Cart_shift(MPI_Comm, int, int, int *, int *);
int MPI_Cart_sub(MPI_Comm,   int *, MPI_Comm *);
int MPI_Cart_map(MPI_Comm, int,   int *,   int *, int *);
int MPI_Graph_map(MPI_Comm, int,   int *,   int *, int *);
int MPI_Get_processor_name(char *, int *);
int MPI_Get_version(int *, int *);
int MPI_Errhandler_create(MPI_Handler_function *, MPI_Errhandler *);
int MPI_Errhandler_set(MPI_Comm, MPI_Errhandler);
int MPI_Errhandler_get(MPI_Comm, MPI_Errhandler *);
int MPI_Errhandler_free(MPI_Errhandler *);
int MPI_Error_string(int, char *, int *);
int MPI_Error_class(int, int *);
double MPI_Wtime(void);
double MPI_Wtick(void);
int MPI_Init(int *, char ***);
int MPI_Finalize(void);
int MPI_Initialized(int *);
$system int MPI_Abort(MPI_Comm, int);


/* Note that we may need to define a @PCONTROL_LIST@ depending on whether 
   stdargs are supported */
int MPI_Pcontrol(const int, ...);

int MPI_DUP_FN ( MPI_Comm, int, void *, void *, void *, int * );


/* MPI-2 functions */

/* Process Creation and Management */
int MPI_Close_port(  char *);
int MPI_Comm_accept(  char *, MPI_Info, int, MPI_Comm, MPI_Comm *);
int MPI_Comm_connect(  char *, MPI_Info, int, MPI_Comm, MPI_Comm *);
int MPI_Comm_disconnect(MPI_Comm *);
int MPI_Comm_get_parent(MPI_Comm *);
int MPI_Comm_join(int, MPI_Comm *);
int MPI_Comm_spawn(  char *, char *[], int, MPI_Info, int, MPI_Comm, MPI_Comm *,
                   int []);
int MPI_Comm_spawn_multiple(int, char *[], char **[],   int [],   MPI_Info [], int,
			    MPI_Comm, MPI_Comm *, int []); 
int MPI_Lookup_name(  char *, MPI_Info, char *);
int MPI_Open_port(MPI_Info, char *);
int MPI_Publish_name(  char *, MPI_Info,   char *);
int MPI_Unpublish_name(  char *, MPI_Info,   char *);

/* One-Sided Communications */
int MPI_Accumulate(  void *, int, MPI_Datatype, int, MPI_Aint, int,
                   MPI_Datatype,  MPI_Op, MPI_Win) ;
int MPI_Get(void *, int, MPI_Datatype, int, MPI_Aint, int, MPI_Datatype,
            MPI_Win) ;
int MPI_Put(  void *, int, MPI_Datatype, int, MPI_Aint, int, MPI_Datatype,
            MPI_Win) ;
int MPI_Win_complete(MPI_Win);
int MPI_Win_create(void *, MPI_Aint, int, MPI_Info, MPI_Comm, MPI_Win *);
int MPI_Win_fence(int, MPI_Win);
int MPI_Win_free(MPI_Win *);
int MPI_Win_get_group(MPI_Win, MPI_Group *);
int MPI_Win_lock(int, int, int, MPI_Win);
int MPI_Win_post(MPI_Group, int, MPI_Win);
int MPI_Win_start(MPI_Group, int, MPI_Win);
int MPI_Win_test(MPI_Win, int *);
int MPI_Win_unlock(int, MPI_Win);
int MPI_Win_wait(MPI_Win);

/* Extended Collective Operations */
int MPI_Alltoallw(  void *,   int [],   int [],
                    MPI_Datatype [], void *,   int [],
		    int [],   MPI_Datatype [], MPI_Comm);
int MPI_Exscan(  void *, void *, int, MPI_Datatype, MPI_Op, MPI_Comm);
 
/* External Interfaces */
int MPI_Add_error_class(int *);
int MPI_Add_error_code(int, int *);
int MPI_Add_error_string(int,   char *);
int MPI_Comm_call_errhandler(MPI_Comm, int);
int MPI_Comm_create_keyval(MPI_Comm_copy_attr_function *, 
  MPI_Comm_delete_attr_function *, int *, void *);
int MPI_Comm_delete_attr(MPI_Comm, int);
int MPI_Comm_free_keyval(int *);
int MPI_Comm_get_attr(MPI_Comm, int, void *, int *);
int MPI_Comm_get_name(MPI_Comm, char *, int *);
int MPI_Comm_set_attr(MPI_Comm, int, void *);
int MPI_Comm_set_name(MPI_Comm,   char *);
int MPI_File_call_errhandler(MPI_File, int);
int MPI_Grequest_complete(MPI_Request);
int MPI_Grequest_start(MPI_Grequest_query_function *, 
                       MPI_Grequest_free_function *, 
                       MPI_Grequest_cancel_function *, void *, MPI_Request *);
int MPI_Init_thread(int *, char ***, int, int *);
int MPI_Is_thread_main(int *);
int MPI_Query_thread(int *);
int MPI_Status_set_cancelled(MPI_Status *, int);
int MPI_Status_set_elements(MPI_Status *, MPI_Datatype, int);
int MPI_Type_create_keyval(MPI_Type_copy_attr_function *, 
  MPI_Type_delete_attr_function *, int *, void *);
int MPI_Type_delete_attr(MPI_Datatype, int);
int MPI_Type_dup(MPI_Datatype, MPI_Datatype *);
int MPI_Type_free_keyval(int *);
int MPI_Type_get_attr(MPI_Datatype, int, void *, int *);
int MPI_Type_get_contents(MPI_Datatype, int, int, int, int [], MPI_Aint [], 
                          MPI_Datatype []);
int MPI_Type_get_envelope(MPI_Datatype, int *, int *, int *, int *);
int MPI_Type_get_name(MPI_Datatype, char *, int *);
int MPI_Type_set_attr(MPI_Datatype, int, void *);
int MPI_Type_set_name(MPI_Datatype,   char *);
int MPI_Type_match_size( int, int, MPI_Datatype *);
int MPI_Win_call_errhandler(MPI_Win, int);
int MPI_Win_create_keyval(MPI_Win_copy_attr_function *, 
  MPI_Win_delete_attr_function *, int *, void *);
int MPI_Win_delete_attr(MPI_Win, int);
int MPI_Win_free_keyval(int *);
int MPI_Win_get_attr(MPI_Win, int, void *, int *);
int MPI_Win_get_name(MPI_Win, char *, int *);
int MPI_Win_set_attr(MPI_Win, int, void *);
int MPI_Win_set_name(MPI_Win,   char *);

/* Miscellany */
MPI_Comm MPI_Comm_f2c(MPI_Fint);
MPI_Datatype MPI_Type_f2c(MPI_Fint);
MPI_File MPI_File_f2c(MPI_Fint);
MPI_Fint MPI_Comm_c2f(MPI_Comm);
MPI_Fint MPI_File_c2f(MPI_File);
MPI_Fint MPI_Group_c2f(MPI_Group);
MPI_Fint MPI_Info_c2f(MPI_Info);
MPI_Fint MPI_Op_c2f(MPI_Op);
MPI_Fint MPI_Request_c2f(MPI_Request);
MPI_Fint MPI_Type_c2f(MPI_Datatype);
MPI_Fint MPI_Win_c2f(MPI_Win);
MPI_Group MPI_Group_f2c(MPI_Fint);
MPI_Info MPI_Info_f2c(MPI_Fint);
MPI_Op MPI_Op_f2c(MPI_Fint);
MPI_Request MPI_Request_f2c(MPI_Fint);
MPI_Win MPI_Win_f2c(MPI_Fint);

int MPI_Alloc_mem(MPI_Aint, MPI_Info info, void *baseptr);
int MPI_Comm_create_errhandler(MPI_Comm_errhandler_function *, MPI_Errhandler *);
int MPI_Comm_get_errhandler(MPI_Comm, MPI_Errhandler *);
int MPI_Comm_set_errhandler(MPI_Comm, MPI_Errhandler);
int MPI_File_create_errhandler(MPI_File_errhandler_function *, MPI_Errhandler *);
int MPI_File_get_errhandler(MPI_File, MPI_Errhandler *);
int MPI_File_set_errhandler(MPI_File, MPI_Errhandler);
int MPI_Finalized(int *);
int MPI_Free_mem(void *);
int MPI_Get_address(  void *, MPI_Aint *);
int MPI_Info_create(MPI_Info *);
int MPI_Info_delete(MPI_Info,   char *);
int MPI_Info_dup(MPI_Info, MPI_Info *);
int MPI_Info_free(MPI_Info *info);
int MPI_Info_get(MPI_Info,   char *, int, char *, int *);
int MPI_Info_get_nkeys(MPI_Info, int *);
int MPI_Info_get_nthkey(MPI_Info, int, char *);
int MPI_Info_get_valuelen(MPI_Info,   char *, int *, int *);
int MPI_Info_set(MPI_Info,   char *,   char *);
int MPI_Pack_external(  char *,   void *, int, MPI_Datatype, void *,
                      MPI_Aint, MPI_Aint *);
int MPI_Pack_external_size(  char *, int, MPI_Datatype, MPI_Aint *);
int MPI_Request_get_status(MPI_Request, int *, MPI_Status *);
int MPI_Status_c2f(  MPI_Status *, MPI_Fint *);
int MPI_Status_f2c(  MPI_Fint *, MPI_Status *);
int MPI_Type_create_darray(int, int, int,   int [],   int [],
                             int [],   int [], int,
                           MPI_Datatype, MPI_Datatype *);
int MPI_Type_create_hindexed(int,   int [],   MPI_Aint [], MPI_Datatype,
                             MPI_Datatype *);
int MPI_Type_create_hvector(int, int, MPI_Aint, MPI_Datatype, MPI_Datatype *);
int MPI_Type_create_indexed_block(int, int,   int [], MPI_Datatype,
                                  MPI_Datatype *);
int MPIX_Type_create_hindexed_block(int, int, const MPI_Aint [], MPI_Datatype, MPI_Datatype *);
int MPI_Type_create_resized(MPI_Datatype, MPI_Aint, MPI_Aint, MPI_Datatype *);
int MPI_Type_create_struct(int,   int [],   MPI_Aint [],
                             MPI_Datatype [], MPI_Datatype *);
int MPI_Type_create_subarray(int,   int [],   int [],   int [],
                             int, MPI_Datatype, MPI_Datatype *);
int MPI_Type_get_extent(MPI_Datatype, MPI_Aint *, MPI_Aint *);
int MPI_Type_get_true_extent(MPI_Datatype, MPI_Aint *, MPI_Aint *);
int MPI_Unpack_external(  char *,   void *, MPI_Aint, MPI_Aint *, void *,
                        int, MPI_Datatype);
int MPI_Win_create_errhandler(MPI_Win_errhandler_function *, MPI_Errhandler *);
int MPI_Win_get_errhandler(MPI_Win, MPI_Errhandler *);
int MPI_Win_set_errhandler(MPI_Win, MPI_Errhandler);

/* Fortran 90-related functions.  These routines are available only if
   Fortran 90 support is enabled 
*/
int MPI_Type_create_f90_integer( int, MPI_Datatype * );
int MPI_Type_create_f90_real( int, int, MPI_Datatype * );
int MPI_Type_create_f90_complex( int, int, MPI_Datatype * );

/* MPI-2.2 functions */
int MPI_Reduce_local(  void *inbuf, void *inoutbuf, int count, MPI_Datatype datatype, MPI_Op op);
int MPI_Op_commutative(MPI_Op op, int *commute);
int MPI_Reduce_scatter_block(  void *sendbuf, void *recvbuf, int recvcount, MPI_Datatype datatype, MPI_Op op, MPI_Comm comm);
int MPI_Dist_graph_create_adjacent(MPI_Comm comm_old, int indegree,   int [],   int [], int outdegree,   int [],   int [], MPI_Info info, int reorder, MPI_Comm *comm_dist_graph);
int MPI_Dist_graph_create(MPI_Comm comm_old, int n,   int [],   int [],   int [],   int [], MPI_Info info, int reorder, MPI_Comm *comm_dist_graph);
int MPI_Dist_graph_neighbors_count(MPI_Comm comm, int *indegree, int *outdegree, int *weighted);
int MPI_Dist_graph_neighbors(MPI_Comm comm, int maxindegree, int [], int [], int maxoutdegree, int [], int []);


/* Permanent key values */
/* C Versions (return pointer to value),
   Fortran Versions (return integer value).
   Handled directly by the attribute value routine
   
   DO NOT CHANGE THESE.  The values encode:
   builtin kind (0x1 in bit 30-31)
   Keyval object (0x9 in bits 26-29)
   for communicator (0x1 in bits 22-25)
   
   Fortran versions of the attributes are formed by adding one to
   the C version.
 */
#define MPI_TAG_UB           0x64400001
#define MPI_HOST             0x64400003
#define MPI_IO               0x64400005
#define MPI_WTIME_IS_GLOBAL  0x64400007
#define MPI_UNIVERSE_SIZE    0x64400009
#define MPI_LASTUSEDCODE     0x6440000b
#define MPI_APPNUM           0x6440000d

/* for info */
#define MPI_INFO_NULL         ((MPI_Info)-1)
#define MPI_MAX_INFO_KEY       255
#define MPI_MAX_INFO_VAL      1024

/* MPI Handles and Constants */
#define MPI_ARGV_NULL 0
#define MPI_ARGVS_NULL 0
#define MPI_BOTTOM (void *)0
extern int * const MPI_UNWEIGHTED;
#define MPI_BSEND_OVERHEAD 88
#define MPI_FILE_NULL (MPI_File *)0
#define MPI_GROUP_EMPTY (MPI_Group *)0
#define MPI_GROUP_NULL (MPI_Group *)0
#define MPI_IN_PLACE  (void *) -1

/* Pre-defined constants */
#define MPI_UNDEFINED      (-32766)
#define MPI_KEYVAL_INVALID 0

/* MPI's error classes */
#define MPI_SUCCESS          0      /* Successful return code */
/* Communication argument parameters */
#define MPI_ERR_BUFFER       1      /* Invalid buffer pointer */
#define MPI_ERR_COUNT        2      /* Invalid count argument */
#define MPI_ERR_TYPE         3      /* Invalid datatype argument */
#define MPI_ERR_TAG          4      /* Invalid tag argument */
#define MPI_ERR_COMM         5      /* Invalid communicator */
#define MPI_ERR_RANK         6      /* Invalid rank */
#define MPI_ERR_ROOT         7      /* Invalid root */
#define MPI_ERR_TRUNCATE    14      /* Message truncated on receive */

/* MPI Objects (other than COMM) */
#define MPI_ERR_GROUP        8      /* Invalid group */
#define MPI_ERR_OP           9      /* Invalid operation */
#define MPI_ERR_REQUEST     19      /* Invalid mpi_request handle */

/* Special topology argument parameters */
#define MPI_ERR_TOPOLOGY    10      /* Invalid topology */
#define MPI_ERR_DIMS        11      /* Invalid dimension argument */

/* All other arguments.  This is a class with many kinds */
#define MPI_ERR_ARG         12      /* Invalid argument */

/* Other errors that are not simply an invalid argument */
#define MPI_ERR_OTHER       15      /* Other error; use Error_string */

#define MPI_ERR_UNKNOWN     13      /* Unknown error */
#define MPI_ERR_INTERN      16      /* Internal error code    */

/* Multiple completion has two special error classes */
#define MPI_ERR_IN_STATUS   17      /* Look in status for error value */
#define MPI_ERR_PENDING     18      /* Pending request */

/* New MPI-2 Error classes */
#define MPI_ERR_FILE        27      /* */
#define MPI_ERR_ACCESS      20      /* */
#define MPI_ERR_AMODE       21      /* */
#define MPI_ERR_BAD_FILE    22      /* */
#define MPI_ERR_FILE_EXISTS 25      /* */
#define MPI_ERR_FILE_IN_USE 26      /* */
#define MPI_ERR_NO_SPACE    36      /* */
#define MPI_ERR_NO_SUCH_FILE 37     /* */
#define MPI_ERR_IO          32      /* */
#define MPI_ERR_READ_ONLY   40      /* */
#define MPI_ERR_CONVERSION  23      /* */
#define MPI_ERR_DUP_DATAREP 24      /* */
#define MPI_ERR_UNSUPPORTED_DATAREP   43  /* */

/* MPI_ERR_INFO is NOT defined in the MPI-2 standard.  I believe that
   this is an oversight */
#define MPI_ERR_INFO        28      /* */
#define MPI_ERR_INFO_KEY    29      /* */
#define MPI_ERR_INFO_VALUE  30      /* */
#define MPI_ERR_INFO_NOKEY  31      /* */

#define MPI_ERR_NAME        33      /* */
#define MPI_ERR_NO_MEM      34      /* Alloc_mem could not allocate memory */
#define MPI_ERR_NOT_SAME    35      /* */
#define MPI_ERR_PORT        38      /* */
#define MPI_ERR_QUOTA       39      /* */
#define MPI_ERR_SERVICE     41      /* */
#define MPI_ERR_SPAWN       42      /* */
#define MPI_ERR_UNSUPPORTED_OPERATION 44 /* */
#define MPI_ERR_WIN         45      /* */

#define MPI_ERR_BASE        46      /* */
#define MPI_ERR_LOCKTYPE    47      /* */
#define MPI_ERR_KEYVAL      48      /* Erroneous attribute key */
#define MPI_ERR_RMA_CONFLICT 49     /* */
#define MPI_ERR_RMA_SYNC    50      /* */ 
#define MPI_ERR_SIZE        51      /* */
#define MPI_ERR_DISP        52      /* */
#define MPI_ERR_ASSERT      53      /* */

#define MPIX_ERR_PROC_FAIL_STOP 54   /* Process failure */

#define MPIX_ERR_RMA_RANGE  55      /* */
#define MPIX_ERR_RMA_ATTACH 56      /* */
#define MPIX_ERR_RMA_SHARED 57      /* */
#define MPIX_ERR_RMA_WRONG_FLAVOR 58    /* */

#define MPI_ERR_LASTCODE    0x3fffffff  /* Last valid error code for a 
					   predefined error class */
/* WARNING: this is also defined in mpishared.h.  Update both locations */
#define MPICH_ERR_LAST_CLASS 58     /* It is also helpful to know the
				       last valid class */
/* End of MPI's error classes */

/* See 4.12.5 for MPI_F_STATUS(ES)_IGNORE */
#define MPIU_DLL_SPEC
extern MPIU_DLL_SPEC MPI_Fint * MPI_F_STATUS_IGNORE;
extern MPIU_DLL_SPEC MPI_Fint * MPI_F_STATUSES_IGNORE;

/* asserts for one-sided communication */
#define MPI_MODE_NOCHECK      1024
#define MPI_MODE_NOSTORE      2048
#define MPI_MODE_NOPUT        4096
#define MPI_MODE_NOPRECEDE    8192
#define MPI_MODE_NOSUCCEED   16384 

/* predefined types for MPIX_Comm_split_type */
#define MPIX_COMM_TYPE_SHARED    1

/* extra const at front would be safer, but is incompatible with MPIX_T_ prototypes */
extern struct MPIR_T_pvar_handle * const MPI_T_PVAR_ALL_HANDLES;

#define MPI_T_ENUM_NULL         ((MPI_T_enum)NULL)
#define MPI_T_CVAR_HANDLE_NULL  ((MPI_T_cvar_handle)NULL)
#define MPI_T_PVAR_HANDLE_NULL  ((MPI_T_pvar_handle)NULL)
#define MPI_T_PVAR_SESSION_NULL ((MPI_T_pvar_session)NULL)

/* the MPI_T_ interface requires that these VERBOSITY constants occur in this
 * relative order with increasing values */
typedef enum MPIR_T_verbosity_t {
    /* don't name-shift this if/when MPI_T_ is accepted, this is an MPICH2-only
     * extension */
    MPI_T_VERBOSITY_INVALID = 0,

    /* arbitrarily shift values to aid debugging and reduce accidental errors */
    MPI_T_VERBOSITY_USER_BASIC = 221,
    MPI_T_VERBOSITY_USER_DETAIL,
    MPI_T_VERBOSITY_USER_ALL,

    MPI_T_VERBOSITY_TUNER_BASIC,
    MPI_T_VERBOSITY_TUNER_DETAIL,
    MPI_T_VERBOSITY_TUNER_ALL,

    MPI_T_VERBOSITY_MPIDEV_BASIC,
    MPI_T_VERBOSITY_MPIDEV_DETAIL,
    MPI_T_VERBOSITY_MPIDEV_ALL
}MPIR_T_verbosity_t;

typedef enum MPIR_T_bind_t {
    /* don't name-shift this if/when MPI_T_ is accepted, this is an MPICH2-only
     * extension */
    MPI_T_BIND_INVALID = 0,

    /* arbitrarily shift values to aid debugging and reduce accidental errors */
    MPI_T_BIND_NO_OBJECT = 9700,
    MPI_T_BIND_MPI_COMM,
    MPI_T_BIND_MPI_DATATYPE,
    MPI_T_BIND_MPI_ERRHANDLER,
    MPI_T_BIND_MPI_FILE,
    MPI_T_BIND_MPI_GROUP,
    MPI_T_BIND_MPI_OP,
    MPI_T_BIND_MPI_REQUEST,
    MPI_T_BIND_MPI_WIN,
    MPI_T_BIND_MPI_MESSAGE,
    MPI_T_BIND_MPI_INFO
}MPIR_T_bind_t;

typedef enum MPIR_T_scope_t {
    /* don't name-shift this if/when MPI_T_ is accepted, this is an MPICH2-only
     * extension */
    MPI_T_SCOPE_INVALID = 0,

    /* arbitrarily shift values to aid debugging and reduce accidental errors */
    MPI_T_SCOPE_READONLY = 60439,
    MPI_T_SCOPE_LOCAL,
    MPI_T_SCOPE_GROUP,
    MPI_T_SCOPE_GROUP_EQ,
    MPI_T_SCOPE_ALL,
    MPI_T_SCOPE_ALL_EQ
}MPIR_T_scope_t;

typedef enum MPIR_T_pvar_class_t {
    /* don't name-shift this if/when MPI_T_ is accepted, this is an MPICH2-only
     * extension */
    MPI_T_PVAR_CLASS_INVALID = 0,

    /* arbitrarily shift values to aid debugging and reduce accidental errors */
    MPI_T_PVAR_CLASS_STATE = 240,
    MPI_T_PVAR_CLASS_LEVEL,
    MPI_T_PVAR_CLASS_SIZE,
    MPI_T_PVAR_CLASS_PERCENTAGE,
    MPI_T_PVAR_CLASS_HIGHWATERMARK,
    MPI_T_PVAR_CLASS_LOWWATERMARK,
    MPI_T_PVAR_CLASS_COUNTER,
    MPI_T_PVAR_CLASS_AGGREGATE,
    MPI_T_PVAR_CLASS_TIMER,
    MPI_T_PVAR_CLASS_GENERIC
}MPIR_T_pvar_class_t;

/* For supported thread levels */
#define MPI_THREAD_SINGLE 0
#define MPI_THREAD_FUNNELED 1
#define MPI_THREAD_SERIALIZED 2
#define MPI_THREAD_MULTIPLE 3

#define MPI_VERSION    "CIVL_MPI"

#endif
