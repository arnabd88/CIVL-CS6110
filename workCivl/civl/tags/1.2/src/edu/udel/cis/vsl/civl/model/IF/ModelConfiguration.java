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
	public static final String UNDEFINED = "UNDEFINED";

	/**
	 * Constant for the name of invalid heap objects.
	 */
	public static final String INVALID = "INVALID";

	public static Set<String> RESERVE_NAMES = new HashSet<>(Arrays.asList(
			UNDEFINED, INVALID));

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
	public static final String SYMBOLIC_CONSTANT_COUNTER = "_X_count_var";

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

	public static final String BUNDLE_TYPE = "$bundle";

	public static final String DYNAMIC_TYPE = "$dynamic";

	public static final String HEAP_TYPE = "$heap";

	public static final String MESSAGE_TYPE = "$message";

	public static final String PROC_TYPE = "$proc";

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

	public static final String NEXT_TIME_COUNT = "$next_time_count";
}
