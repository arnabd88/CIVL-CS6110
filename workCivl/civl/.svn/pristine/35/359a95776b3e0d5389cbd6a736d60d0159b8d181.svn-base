package edu.udel.cis.vsl.civl.config.IF;

import static edu.udel.cis.vsl.gmc.Option.OptionType.BOOLEAN;
import static edu.udel.cis.vsl.gmc.Option.OptionType.INTEGER;
import static edu.udel.cis.vsl.gmc.Option.OptionType.STRING;

import java.io.File;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;

import edu.udel.cis.vsl.gmc.Option;
import edu.udel.cis.vsl.gmc.Option.OptionType;

/**
 * This class manages all constant configurations of the system.
 * 
 * NOTE: when you add a new option, add it here, give it name ending in "O",
 * like the others, AND add it to the list in method {@link #getAllOptions()}.
 * And keep them in alphabetical order.
 * 
 * @author Manchun Zheng
 * 
 */
public class CIVLConstants {

	/**
	 * Kinds of deadlock: absolute, potential or none.
	 * 
	 * @author Manchun Zheng
	 *
	 */
	public enum DeadlockKind {
		ABSOLUTE, POTENTIAL, NONE
	}

	/**
	 * Where the CIVL header files (suffix .h and .cvh) and associated
	 * implementations (.cvl) are located. This path is relative to the class
	 * path. Since the "include" directory is in the class path, this will cause
	 * ABC to look in include/civl.
	 */
	public final static File CIVL_INCLUDE_PATH = new File(new File(
			File.separator + "include"), "civl");

	/** The version of this release of CIVL. */
	public final static String version = "1.5";

	/**
	 * The date of this release of CIVL. Format: YYYY-MM-DD in accordance with
	 * ISO 8601.
	 */
	public final static String date = "2015-10-31";

	/**
	 * The prefix of the full name of the class of a library enabler/executor.
	 */
	public final static String LIBRARY_PREFIX = "edu.udel.cis.vsl.civl.library.";

	/**
	 * A string printed before and after titles of sections of output to make
	 * them stand out among the clutter.
	 */
	public final static String bar = "===================";

	public final static String statsBar = "===";

	/**
	 * The name of the directory into which CIVL will store the artifacts it
	 * generates.
	 */
	public final static String CIVLREP = "CIVLREP";

	/**
	 * Number of seconds between printing of update messages.
	 */
	public final static int consoleUpdatePeriod = 15;

	/**
	 * Number of seconds between saving update messages to disk when in web app
	 * mode.
	 */
	public final static int webUpdatePeriod = 1;

	/**
	 * Debug option, false by default.
	 */
	public final static Option debugO = Option.newScalarOption("debug",
			BOOLEAN, "debug mode: print very detailed information", false);

	public final static Option timeoutO = Option.newScalarOption("timeout",
			OptionType.INTEGER,
			"time out in seconds, default is never time out", -1);

	/**
	 * Debug option, false by default.
	 */
	public final static Option checkDivisionByZeroO = Option.newScalarOption(
			"checkDivisionByZero", BOOLEAN, "check division-by-zero?", true);

	/**
	 * Debug option, false by default.
	 */
	public final static Option checkMemoryLeakO = Option.newScalarOption(
			"checkMemoryLeak", BOOLEAN, "check memory-leak errors?", true);

	/**
	 * Prints the command line? false by default.
	 */
	public final static Option echoO = Option.newScalarOption("echo", BOOLEAN,
			"print the command line", false);

	/**
	 * Enables printf? true by default. When false, nothing is printed for
	 * printf function.
	 */
	public final static Option enablePrintfO = Option.newScalarOption(
			"enablePrintf", BOOLEAN, "enable printf function", true);

	/**
	 * The maximal number of errors allowed before terminating CIVL. 1 by
	 * default.
	 */
	public final static Option errorBoundO = Option.newScalarOption(
			"errorBound", INTEGER, "stop after finding this many errors", 1);

	/**
	 * User guided simulation?
	 */
	public final static Option guidedO = Option.newScalarOption("guided",
			BOOLEAN, "user guided simulation; applies only to run, ignored\n"
					+ "    for all other commands", null);

	/**
	 * The id of the trace for replay, 0 by default.
	 */
	public final static Option idO = Option.newScalarOption("id", INTEGER,
			"ID number of trace to replay; applies only to replay command", 0);

	/**
	 * Specify values of input variables.
	 */
	public final static Option inputO = Option
			.newMapOption("input",
					"initialize input variable KEY to VALUE; applies only to run and verify");

	/**
	 * The maximal depth for search. Infinite by default.
	 */
	public final static Option maxdepthO = Option.newScalarOption("maxdepth",
			INTEGER, "bound on search depth", Integer.MAX_VALUE);

	/**
	 * Search for the minimum counterexample? false by default.
	 */
	public final static Option minO = Option.newScalarOption("min", BOOLEAN,
			"search for minimal counterexample", false);

	public final static Option mpiContractO = Option.newScalarOption(
			"mpiContract", BOOLEAN, "enable contracts for MPI mode", false);

	/**
	 * The bound on number of live processes (no bound if negative). No bound by
	 * default.
	 */
	public final static Option procBoundO = Option.newScalarOption("procBound",
			INTEGER,
			"bound on number of live processes (no bound if negative)", -1);

	/**
	 * TODO can it be cleaned up? Select enabled transitions randomly? Default
	 * for run.
	 */
	public final static Option randomO = Option.newScalarOption("random",
			BOOLEAN, "select enabled transitions randomly; default for run,\n"
					+ "    ignored for all other commands", null);

	/**
	 * Save states during depth-first search? true by default.
	 */
	public final static Option saveStatesO = Option.newScalarOption(
			"saveStates", BOOLEAN, "save states during depth-first search",
			true);

	/**
	 * Set the random seed for run mode.
	 */
	public final static Option seedO = Option.newScalarOption("seed", STRING,
			"set the random seed; applies only to run", null);

	/**
	 * Analyze abs calls? false by default.
	 */
	public final static Option analyzeAbsO = Option.newScalarOption(
			"analyze_abs", BOOLEAN, "analyze abs calls? false by default",
			false);

	/**
	 * Show the AST of the program? false by default.
	 */
	public final static Option astO = Option.newScalarOption("ast", BOOLEAN,
			"print the AST of the program", false);

	/**
	 * Print the ample set when it contains more than one processes? false by
	 * default.
	 */
	public final static Option showAmpleSetO = Option.newScalarOption(
			"showAmpleSet", BOOLEAN,
			"print the ample set when it contains more than one processes",
			false);

	/**
	 * Print ample set and state when ample set contains more than one
	 * processes? false by default.
	 */
	public final static Option showAmpleSetWtStatesO = Option.newScalarOption(
			"showAmpleSetWtStates", BOOLEAN,
			"print ample set and state when ample set contains >1 processes",
			false);

	/**
	 * Print the impact/reachable memory units when the state contains more than
	 * one processes? false by default.
	 */
	public final static Option showMemoryUnitsO = Option
			.newScalarOption(
					"showMemoryUnits",
					BOOLEAN,
					"print the impact/reachable memory units when the state contains more than one processes",
					false);

	/**
	 * Show the CIVL model of the program? false by default.
	 */
	public final static Option showModelO = Option.newScalarOption("showModel",
			BOOLEAN, "print the model", false);

	/**
	 * Show theorem prover queries? false by default.
	 */
	public final static Option showProverQueriesO = Option.newScalarOption(
			"showProverQueries", BOOLEAN, "print theorem prover queries only",
			false);

	/**
	 * Show all SARL queries? false by default.
	 */
	public final static Option showQueriesO = Option.newScalarOption(
			"showQueries", BOOLEAN, "print all queries", false);

	/**
	 * Show all states that are saved? false by default.
	 */
	public final static Option showSavedStatesO = Option.newScalarOption(
			"showSavedStates", BOOLEAN, "print saved states only", false);

	/**
	 * Show all states? false by default.
	 */
	public final static Option showStatesO = Option.newScalarOption(
			"showStates", BOOLEAN, "print all states", false);

	/**
	 * Show the time used by each translation phase? false by default.
	 */
	public final static Option showTimeO = Option.newScalarOption("showTime",
			BOOLEAN, "print timings", false);

	/**
	 * Show all transitions? false by default;
	 */
	public final static Option showTransitionsO = Option.newScalarOption(
			"showTransitions", BOOLEAN, "print transitions", false);

	/**
	 * Show unreachable code? false by default;
	 */
	public final static Option showUnreachedCodeO = Option.newScalarOption(
			"showUnreached", BOOLEAN, "print the unreachable code", false);

	/**
	 * Simplify states using path conditions? true by default.
	 */
	public final static Option simplifyO = Option.newScalarOption("simplify",
			BOOLEAN, "simplify states?", true);

	/**
	 * Try to solve for concrete counterexample? false by default.
	 */
	public final static Option solveO = Option.newScalarOption("solve",
			BOOLEAN, "try to solve for concrete counterexample", false);

	/**
	 * Don't modify file system when running printf? true by default.
	 */
	public final static Option statelessPrintfO = Option.newScalarOption(
			"statelessPrintf", BOOLEAN,
			"prevent printf function modifying the file system", true);

	/**
	 * Print the impact/reachable memory units when the state contains more than
	 * one processes? false by default.
	 */
	public final static Option strictCompareO = Option.newScalarOption(
			"strict", BOOLEAN, "check strict functional equivalence?", true);

	/**
	 * skip non-pthread programs?
	 */
	public final static Option pthreadOnlyO = Option
			.newScalarOption(
					"pthreadOnly",
					BOOLEAN,
					"skip non-pthread programs? Only valid when -svcomp is true.",
					true);

	/**
	 * Set the system include path.
	 */
	public final static Option sysIncludePathO = Option.newScalarOption(
			"sysIncludePath", STRING,
			"set the system include path, using : to separate multiple paths",
			null);

	/**
	 * File name of trace to replay
	 */
	public final static Option traceO = Option.newScalarOption("trace", STRING,
			"filename of trace to replay", null);

	/**
	 * Sets user include path.
	 */
	public final static Option userIncludePathO = Option.newScalarOption(
			"userIncludePath", STRING,
			"set the user include path, using : to separate multiple paths",
			null);

	/**
	 * Verbose mode? false by default
	 */
	public final static Option verboseO = Option.newScalarOption("verbose",
			BOOLEAN, "verbose mode", false);

	/**
	 * Launch gui? false by default.
	 */
	public final static Option guiO = Option.newScalarOption("gui", BOOLEAN,
			"launch GUI? (under development, only works with replay)", false);

	/**
	 * What kind of deadlock is to be checked, potential, absolute or none?
	 * absolute by default.
	 */
	public final static Option deadlockO = Option.newScalarOption("deadlock",
			STRING, "deadlock kind? (potential|absolute|none)", "absolute");

	/**
	 * Perform svcomp transformation? false by default.
	 */
	public final static Option svcomp16O = Option.newScalarOption("svcomp16",
			BOOLEAN, "translate program for sv-comp 2016?", false);

	/**
	 * Show the input variables of this model? false by default.
	 */
	public final static Option showInputVarsO = Option
			.newScalarOption("showInputs", BOOLEAN,
					"show input variables of my program?", false);

	/**
	 * Show the preprocessing result? false by default.
	 */
	public final static Option preprocO = Option.newScalarOption("preproc",
			BOOLEAN, "show the preprocessing result?", false);

	/**
	 * Show the program after all applicable transformations? false by default.
	 */
	public final static Option showProgramO = Option.newScalarOption(
			"showProgram", BOOLEAN, "show my program after transformations?",
			false);

	/**
	 * Show the path condition of each state? false by default.
	 */
	public final static Option showPathConditionO = Option.newScalarOption(
			"showPathCondition", BOOLEAN,
			"show the path condition of each state?", false);

	/**
	 * Don't simplify OpenMP pragmas? false by default.
	 */
	public final static Option ompNoSimplifyO = Option.newScalarOption(
			"ompNoSimplify", BOOLEAN, "don't simplify omp pragmas", false);

	/**
	 * Collect output? false by default.
	 */
	public final static Option collectOutputO = Option.newScalarOption(
			"collectOutput", BOOLEAN, "collect output?", false);

	/**
	 * Collect processes? true by default.
	 */
	public final static Option collectProcessesO = Option.newScalarOption(
			"collectProcesses", BOOLEAN, "collect processes?", true);

	/**
	 * Collect scopes? true by default.
	 */
	public final static Option collectScopesO = Option.newScalarOption(
			"collectScopes", BOOLEAN, "collect dyscopes?", true);

	/**
	 * Collect heaps? true by default.
	 */
	public final static Option collectHeapsO = Option.newScalarOption(
			"collectHeaps", BOOLEAN, "collect heaps?", true);

	/**
	 * Link a source file with the target program.
	 */
	public final static Option linkO = Option.newScalarOption("link", STRING,
			"link a source file with the target program", null);

	/**
	 * Define macros.
	 */
	public final static Option macroO = Option.newMapOption("D",
			"macro definitions: <macro> or <macro>=<object>");

	/**
	 * Write output for web app? false by default.
	 */
	public final static Option webO = Option.newScalarOption("web", BOOLEAN,
			"write output for web app?", false);

	/**
	 * Set the loop decomposition strategy for OpenMP transformer. Round robin
	 * by default.
	 */
	public final static Option ompLoopDecompO = Option.newScalarOption(
			"ompLoopDecomp", STRING,
			"loop decomposition strategy? (ALL|ROUND_ROBIN|RANDOM)",
			"ROUND_ROBIN");

	/**
	 * Collect heaps? true by default.
	 */
	public final static Option CIVLMacroO = Option.newScalarOption("_CIVL",
			BOOLEAN, "Define _CIVL macro?", true);

	/**
	 * The name of the CIVL system function, which is the starting point of a
	 * CIVL model.
	 */
	public final static String civlSystemFunction = "_CIVL_system";

	/**
	 * Returns all options defined for CIVL in alphabetic order.
	 * 
	 * @return all options defined for CIVL in alphabetic order.
	 */
	public final static Option[] getAllOptions() {
		return new Option[] { astO, collectHeapsO, collectProcessesO,
				collectScopesO, deadlockO, debugO, echoO, enablePrintfO,
				errorBoundO, guiO, guidedO, idO, inputO, linkO, macroO,
				maxdepthO, minO, mpiContractO, ompLoopDecompO, ompNoSimplifyO,
				preprocO, procBoundO, randomO, saveStatesO, seedO,
				showAmpleSetO, showAmpleSetWtStatesO, showInputVarsO,
				showMemoryUnitsO, showModelO, showPathConditionO, showProgramO,
				showProverQueriesO, showQueriesO, showSavedStatesO,
				showStatesO, showTimeO, showTransitionsO, showUnreachedCodeO,
				simplifyO, solveO, statelessPrintfO, svcomp16O, pthreadOnlyO,
				sysIncludePathO, traceO, userIncludePathO, verboseO, webO,
				CIVLMacroO, analyzeAbsO, strictCompareO, collectOutputO,
				checkDivisionByZeroO, checkMemoryLeakO, timeoutO };
	}

	// headers...
	public final static String CIVLC = "civlc.cvh";
	public final static String CIVL_MPI = "civl-mpi.cvh";
	public final static String CIVL_PTHREAD = "civl-pthread.cvh";
	public final static String COMM = "comm.cvh";
	public final static String CONCURRENCY = "concurrency.cvh";
	public final static String CIVL_OMP = "civl-omp.cvh";
	// public final static String CIVL_DOMAIN = "domain.cvh";
	public final static String MPI = "mpi.h";
	public final static String MATH = "math.h";
	public final static String OMP = "omp.h";
	public final static String PTHREAD = "pthread.h";
	public final static String SEQ = "seq.cvh";
	public final static String STRING_LIB = "string.h";
	public final static String SVCOMP = "svcomp.h";
	public final static String STDIO = "stdio.h";
	public final static String STDLIB = "stdlib.h";
	public final static String SYS_TIME = "sys/time.h";
	public final static String SYS_TIMES = "sys/times.h";
	public final static String TIME = "time.h";
	public final static String CUDA = "cuda.h";
	public final static String CIVL_CUDA = "civl-cuda.cvh";

	public final static String ASSERT = "assert.h";
	public final static String COMPLEX = "complex.h";
	public final static String CTYPE = "ctype.h";
	public final static String FLOAT = "float.h";
	public final static String GD = "gd.h";
	public final static String GDFX = "gdfx.h";
	public final static String LIMITS = "limits.h";
	public final static String OP = "op.h";
	public final static String STDARG = "stdarg.h";
	public final static String STDBOOL = "stdbool.h";
	public final static String STDDEF = "stddef.h";
	public final static String STDINT = "stdint.h";
	public final static String UNISTD = "unistd.h";

	/**
	 * Returns all CIVL-C libraries.
	 * 
	 * @return all CIVL-C libraries.
	 */
	public final static Set<String> getAllCivlLibs() {
		return new HashSet<String>(Arrays.asList(CIVLC, CIVL_MPI, CIVL_PTHREAD,
				COMM, CONCURRENCY, CIVL_OMP, SEQ, CIVL_CUDA));
	}

	/**
	 * Returns all standard c libraries.
	 * 
	 * @return all standard c libraries.
	 */
	public final static Set<String> getCinterfaces() {
		return new HashSet<String>(Arrays.asList(MPI, MATH, OMP, PTHREAD,
				STRING_LIB, SVCOMP, STDIO, STDLIB, TIME, CUDA, SYS_TIME,
				UNISTD, STDINT));
	}

	/**
	 * Returns all standard c libraries.
	 * 
	 * @return all standard c libraries.
	 */
	public final static Set<String> getAllCLibraries() {
		return new HashSet<String>(Arrays.asList(MPI, MATH, OMP, PTHREAD,
				STRING_LIB, SVCOMP, STDIO, STDLIB, TIME, CUDA, SYS_TIME,
				ASSERT, COMPLEX, CTYPE, FLOAT, GD, GDFX, LIMITS, OP, STDARG,
				STDBOOL, STDDEF, UNISTD));
	}
}
