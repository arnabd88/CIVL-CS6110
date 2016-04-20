package edu.udel.cis.vsl.civl.model.IF;

import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;

/**
 * This file contains the constants used by the model builder/translator, which
 * reflects the translation strategy of CIVL. For example, for every scope, the
 * heap variable is added as the variable with index 0.
 * 
 * @author zmanchun
 * 
 */
public final class ModelConfiguration {

	/* Reserved names of symbolic constants */
	public final static String GENERAL_ROOT = "_gen_root";
	/**
	 * Constant for the name of undefined values
	 */
	public static final String UNDEFINED = "UNDEFINED";

	/**
	 * Constant for the name of invalid heap objects.
	 */
	public static final String INVALID = "INVALID";

	/**
	 * the set of reserved names for symbolic constants
	 */
	public static Set<String> RESERVE_NAMES = new HashSet<>(Arrays.asList(
			UNDEFINED, INVALID));

	/**
	 * add new name to the reserved name set
	 * 
	 * @param name
	 *            name to be added to the reserved name set
	 */
	public static void addReservedName(String name) {
		if (!RESERVE_NAMES.contains(name))
			RESERVE_NAMES.add(name);
	}

	/* Domain decomposition strategies */
	/**
	 * ALL, corresponds to the enumerator ALL of the enumeration type
	 * $domain_decomposition.
	 */
	public static final int DECOMP_ALL = 0;

	/**
	 * RANDOM, corresponds to the enumerator ALL of the enumeration type
	 * $domain_decomposition.
	 */
	public static final int DECOMP_RANDOM = 1;

	/**
	 * ROUND_ROBIN, corresponds to the enumerator ALL of the enumeration type
	 * $domain_decomposition.
	 */
	public static final int DECOMP_ROUND_ROBIN = 2;

	/* System variables */

	/**
	 * The name of the atomic lock variable of the system scope.
	 */
	public static final String ATOMIC_LOCK_VARIABLE = "_atomic_lock_var";

	/**
	 * The name of the time count variable, which is incremented by the system
	 * function $next_time_count() of civlc.cvh.
	 */
	public static final String TIME_COUNT_VARIABLE = "_time_count_var";

	/**
	 * The variable to store broken time information for the time library. This
	 * variable is needed because some functions of time.h returns a pointer to
	 * it.
	 */
	public static final String BROKEN_TIME_VARIABLE = "_broken_time_var";

	/**
	 * The variable to store the number of symbolic constants appearing in the
	 * state
	 */
	public static final String SYMBOLIC_CONSTANT_COUNTER = "_Y_count_var";

	/**
	 * The variable to store the number of symbolic constants appearing in the
	 * state
	 */
	public static final String SYMBOLIC_INPUT_COUNTER = "_X_count_var";

	/**
	 * The name of the heap variable of each scope.
	 */
	public static final String HEAP_VAR = "_heap";

	/**
	 * The index of the heap variable in the scope.
	 */
	public static final int heapVariableIndex = 0;

	/**
	 * The name of the file system variable, created when stdio transformation
	 * is performed.
	 */
	public static final String FILE_SYSTEM_TYPE = "CIVL_filesystem";

	/* Types */

	/**
	 * The name of the $range type.
	 */
	public static final String RANGE_TYPE = "$range";

	/**
	 * The name of _pthread_gpool_t type, which is the object type of the handle
	 * $pthread_gpool, and is used by pthread.cvl.
	 */
	public static final String PTHREAD_GPOOL = "_pthread_gpool_t";

	/**
	 * The name of _pthread_poo_t type, which is the object type of the handle
	 * $pthread_pool, and is used by pthread.cvl.
	 */
	public static final String PTHREAD_POOL = "_pthread_pool_t";

	/**
	 * The name of __barrier__ type, which is the object type of the handle
	 * $barrier.
	 */
	public static final String BARRIER_TYPE = "$barrier";

	/**
	 * the name of $bundle type
	 */
	public static final String BUNDLE_TYPE = "$bundle";

	/**
	 * the name of $dynamic type
	 */
	public static final String DYNAMIC_TYPE = "$dynamic";

	/**
	 * the name of the heap type
	 */
	public static final String HEAP_TYPE = "$heap";

	/**
	 * the name of message type
	 */
	public static final String MESSAGE_TYPE = "$message";

	/**
	 * the name of process reference type
	 */
	public static final String PROC_TYPE = "$proc";

	/**
	 * the name of queue type
	 */
	public static final String QUEUE_TYPE = "$queue";

	/**
	 * The name of $comm type, which is the object type of the handle $comm.
	 */
	public static final String COMM_TYPE = "$comm";

	/**
	 * The name of __gbarrier__ type, which is the object type of the handle
	 * $gbarrier.
	 */
	public static final String GBARRIER_TYPE = "$gbarrier";

	/**
	 * The name of __gcomm__ type, which is the object type of the handle
	 * $gcomm.
	 */
	public static final String GCOMM_TYPE = "$gcomm";

	/**
	 * The name of __int_iter__ type, which is the object type of the handle
	 * $int_iter.
	 */
	public static final String INT_ITER_TYPE = "$int_iter";

	/**
	 * The file type $file.
	 */
	public static final String REAL_FILE_TYPE = "$file";

	/**
	 * The file reference type FILE.
	 */
	public static final String FILE_STREAM_TYPE = "FILE";

	/**
	 * The tm type, used by time.h.
	 */
	public static final String TM_TYPE = "tm";

	/**
	 * The <code>__collect_record__</code> type
	 */
	public static final String COLLECT_RECORD_TYPE = "$collect_record";

	/**
	 * The <code>__gcollect_checker__</code> type
	 */
	public static final String GCOLLECT_CHECKER_TYPE = "$gcollect_checker";

	/**
	 * The <code>__collect_checker__</code> type
	 */
	public static final String COLLECT_CHECKER_TYPE = "$collect_checker";

	/* libraries */

	/**
	 * The name of the time.h library.
	 */
	public static final String TIME_LIB = "time.h";

	/* Functions */

	/**
	 * the function to get the unique counter of time
	 */
	public static final String NEXT_TIME_COUNT = "$next_time_count";

	/**
	 * name of the symbolic type for mapping user-defined types to integers
	 */
	public static final String DYNAMIC_TYPE_NAME = "dynamicType";

	/**
	 * prefix for anonymous variables
	 */
	public static final String ANONYMOUS_VARIABLE_PREFIX = "_anon_";

	// TODO: following constant can replace ones in MPI2CIVLWorker
	/**
	 * The name of the identifier of the MPI_Comm variable in the final CIVL
	 * program.
	 */
	public final static String COMM_WORLD = "MPI_COMM_WORLD";

	/**
	 * The name of the identifier of the CMPI_Gcomm variable in the final CIVL
	 * program.
	 */
	public final static String GCOMM_WORLD = "_mpi_gcomm";

	/**
	 * The name of the identifier of the CMPI_Gcomm sequence variable in the
	 * final CIVL-MPI program
	 */
	public final static String GCOMMS = "_mpi_gcomms";

	/**
	 * The name of the variable representing the status of an MPI process, which
	 * is modified by MPI_Init() and MPI_Finalized().
	 */
	public final static String MPI_SYS_STATUS = "_mpi_status";

	/**
	 * The name of the input variable denoting the number of MPI processes in
	 * the final CIVL-C program.
	 */
	public final static String NPROCS = "_mpi_nprocs";

	/**
	 * The name of the input variable denoting the upper bound of the number of
	 * MPI processes in the final CIVL-C program.
	 */
	public final static String NPROCS_UPPER_BOUND = "_mpi_nprocs_hi";

	/**
	 * The name of the input variable denoting the lower bound of the number of
	 * MPI processes in the final CIVL-C program.
	 */
	public final static String NPROCS_LOWER_BOUND = "_mpi_nprocs_lo";
}
