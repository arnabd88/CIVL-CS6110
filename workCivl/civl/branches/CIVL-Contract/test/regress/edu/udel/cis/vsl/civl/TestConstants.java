package edu.udel.cis.vsl.civl;

/**
 * 
 * This class contains all the constants used in test files
 * 
 *
 */
public class TestConstants {

	/**
	 * commands
	 */
	public static String RUN = "run";

	public static String VERIFY = "verify";

	public static String REPLAY = "replay";

	public static String COMPARE = "compare";
	
	public static String SHOW = "show";

	/**
	 * options
	 */
	public static String QUIET = "-quiet";

	public static String IMPL = "-impl";

	public static String SPEC = "-spec";

	public static String NO_PRINTF = "-enablePrintf=false";
	
	public static String SHOW_UNREACHED = "-showUnreached=true";
	
	public static String ANALYZE_ABS = "-analyze_abs=true";
	
	public static String MIN = "-min";
	
	public static String DMATH_ELABORATE_ASSUMPTIONS = "-DMATH_ELABORATE_ASSUMPTIONS";
	
	public static String DMATH_NO_ASSUMPTIONS = "-DMATH_NO_ASSUMPTIONS";
	
	public static String SHOW_PROGRAM = "-showProgram=true";
	
	public static String SHOW_SAVED_STATES = "-showSavedStates=true";
	
	public static String NO_SHOW_SAVED_STATES = "-showSavedStates=false";
	
	public static String SHOW_TRANSITIONS = "-showTransitions=true";
	
	public static String NO_SHOW_TRANSITIONS = "-showTransitions=false";
	
	public static String POTENTIAL_DEADLOCK = "-deadlock=potential";
	
	public static String MPI_CONTRACT = "-mpiContract=true";
	
	public static String SHOW_MODEL = "-showModel=true";
	
	public static String CHECK_DIVISION_BY_ZERO = "-checkDivisionByZero=true";
	
	public static String NO_CHECK_DIVISION_BY_ZERO = "-checkDivisionByZero=false";
	
	public static String errorBound(int bound){
		return "-errorBound=" + bound;
	}
	
	public static String procBound(int bound){
		return "-procBound=" + bound;
	}

}
