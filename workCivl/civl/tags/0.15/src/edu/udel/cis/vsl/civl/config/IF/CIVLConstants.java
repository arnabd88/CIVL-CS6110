package edu.udel.cis.vsl.civl.config.IF;

import static edu.udel.cis.vsl.gmc.Option.OptionType.BOOLEAN;
import static edu.udel.cis.vsl.gmc.Option.OptionType.INTEGER;
import static edu.udel.cis.vsl.gmc.Option.OptionType.STRING;

import java.util.LinkedList;
import java.util.List;

import edu.udel.cis.vsl.gmc.Option;

/**
 * This class manages all constant configurations of the system.
 * 
 * @author Manchun Zheng
 * 
 */
public class CIVLConstants {
	/** The version of this release of CIVL. */
	public final static String version = "0.15";

	/**
	 * The date of this release of CIVL. Format: YYYY-MM-DD in accordance with
	 * ISO 8601.
	 */
	public final static String date = "2014-12-23";

	/**
	 * The prefix of the full name of the class of a library enabler/executor.
	 */
	public final static String LIBRARY_PREFIX = "edu.udel.cis.vsl.civl.library.";

	/**
	 * A string printed before and after titles of sections of output to make
	 * them stand out among the clutter.
	 */
	public final static String bar = "===================";

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

	public final static Option debugO = Option.newScalarOption("debug",
			BOOLEAN, "debug mode: print very detailed information", false);

	public final static Option echoO = Option.newScalarOption("echo", BOOLEAN,
			"print the command line", false);

	public final static Option enablePrintfO = Option.newScalarOption(
			"enablePrintf", BOOLEAN, "enable printf function", true);

	public final static Option errorBoundO = Option.newScalarOption(
			"errorBound", INTEGER, "stop after finding this many errors", 1);

	public final static Option guidedO = Option.newScalarOption("guided",
			BOOLEAN, "user guided simulation; applies only to run, ignored\n"
					+ "    for all other commands", null);

	public final static Option idO = Option.newScalarOption("id", INTEGER,
			"ID number of trace to replay; applies only to replay command", 0);

	public final static Option inputO = Option
			.newMapOption("input",
					"initialize input variable KEY to VALUE; applies only to run and verify");

	public final static Option maxdepthO = Option.newScalarOption("maxdepth",
			INTEGER, "bound on search depth", Integer.MAX_VALUE);

	public final static Option minO = Option.newScalarOption("min", BOOLEAN,
			"search for minimal counterexample", false);

	public final static Option randomO = Option.newScalarOption("random",
			BOOLEAN, "select enabled transitions randomly; default for run,\n"
					+ "    ignored for all other commands", null);

	public final static Option saveStatesO = Option.newScalarOption(
			"saveStates", BOOLEAN, "save states during depth-first search",
			true);

	public final static Option seedO = Option.newScalarOption("seed", STRING,
			"set the random seed; applies only to run", null);

	public final static Option astO = Option.newScalarOption("ast", BOOLEAN,
			"print the AST of the program", false);

	public final static Option showAmpleSetO = Option.newScalarOption(
			"showAmpleSet", BOOLEAN,
			"print the ample set when it contains more than one processes",
			false);

	public final static Option showAmpleSetWtStatesO = Option
			.newScalarOption(
					"showAmpleSetWtStates",
					BOOLEAN,
					"print the ample set and the state when there are more than one processes in the ample set",
					false);

	public final static Option showModelO = Option.newScalarOption("showModel",
			BOOLEAN, "print the model", false);

	public final static Option showProverQueriesO = Option.newScalarOption(
			"showProverQueries", BOOLEAN, "print theorem prover queries only",
			false);

	public final static Option showQueriesO = Option.newScalarOption(
			"showQueries", BOOLEAN, "print all queries", false);

	public final static Option showSavedStatesO = Option.newScalarOption(
			"showSavedStates", BOOLEAN, "print saved states only", false);

	public final static Option showStatesO = Option.newScalarOption(
			"showStates", BOOLEAN, "print all states", false);

	public final static Option showTimeO = Option.newScalarOption("showTime",
			BOOLEAN, "print timings", false);

	public final static Option showTransitionsO = Option.newScalarOption(
			"showTransitions", BOOLEAN, "print transitions", false);

	public final static Option simplifyO = Option.newScalarOption("simplify",
			BOOLEAN, "simplify states?", true);

	public final static Option solveO = Option.newScalarOption("solve",
			BOOLEAN, "try to solve for concrete counterexample", false);

	public final static Option statelessPrintfO = Option.newScalarOption(
			"statelessPrintf", BOOLEAN,
			"prevent printf function modifying the file system", true);

	public final static Option sysIncludePathO = Option.newScalarOption(
			"sysIncludePath", STRING, "set the system include path", null);

	public final static Option traceO = Option.newScalarOption("trace", STRING,
			"filename of trace to replay", null);

	public final static Option userIncludePathO = Option.newScalarOption(
			"userIncludePath", STRING, "set the user include path", null);

	public final static Option verboseO = Option.newScalarOption("verbose",
			BOOLEAN, "verbose mode", false);

	public final static Option guiO = Option.newScalarOption("gui", BOOLEAN,
			"launch GUI? (under development, only works with replay)", false);

	public final static Option deadlockO = Option.newScalarOption("deadlock",
			STRING, "deadlock kind? (potential|absolute|none)", "absolute");

	public final static Option svcompO = Option.newScalarOption("svcomp",
			BOOLEAN, "translate program for sv-comp?", false);

	public final static Option showInputVarsO = Option
			.newScalarOption("showInputs", BOOLEAN,
					"show input variables of my program?", false);

	public final static Option preprocO = Option.newScalarOption("preproc",
			BOOLEAN, "show the preprocessing result?", false);

	public final static Option showProgramO = Option.newScalarOption(
			"showProgram", BOOLEAN, "show my program after transformations?",
			false);

	public final static Option showPathConditionO = Option.newScalarOption(
			"showPathCondition", BOOLEAN,
			"show the path condition of each state?", false);

	public final static Option ompNoSimplifyO = Option.newScalarOption(
			"ompNoSimplify", BOOLEAN, "don't simplify omp pragmas", false);

	public final static Option collectProcessesO = Option.newScalarOption(
			"collectProcesses", BOOLEAN, "collect processes?", true);

	public final static Option collectScopesO = Option.newScalarOption(
			"collectScopes", BOOLEAN, "collect dyscopes?", true);

	public final static Option collectHeapsO = Option.newScalarOption(
			"collectHeaps", BOOLEAN, "collect heaps?", true);

	public final static Option linkO = Option.newScalarOption("link", STRING,
			"link a source file with the target program", null);

	public final static Option macroO = Option.newMapOption("D",
			"macro definitions: <macro> or <macro>=<object>");

	public final static Option webO = Option.newScalarOption("web", BOOLEAN,
			"write output for web app?", false);

	public final static String civlSystemFunction = "_CIVL_system";

	public static Option[] getAllOptions() {
		int numOpts = 32;
		List<Option> outputs = new LinkedList<Option>();

		outputs.add(CIVLConstants.deadlockO);
		outputs.add(CIVLConstants.debugO);
		outputs.add(CIVLConstants.echoO);
		outputs.add(CIVLConstants.enablePrintfO);
		outputs.add(CIVLConstants.errorBoundO);
		outputs.add(CIVLConstants.guidedO);
		// outputs.add(CIVLConstants.guiO);
		outputs.add(CIVLConstants.idO);
		outputs.add(CIVLConstants.maxdepthO);
		outputs.add(CIVLConstants.minO);
		outputs.add(CIVLConstants.randomO);
		outputs.add(CIVLConstants.saveStatesO);
		outputs.add(CIVLConstants.seedO);
		outputs.add(CIVLConstants.showAmpleSetO);
		outputs.add(CIVLConstants.showAmpleSetWtStatesO);
		outputs.add(CIVLConstants.showInputVarsO);
		outputs.add(CIVLConstants.showModelO);
		outputs.add(CIVLConstants.showPathConditionO);
		outputs.add(CIVLConstants.showProgramO);
		outputs.add(CIVLConstants.showProverQueriesO);
		outputs.add(CIVLConstants.showQueriesO);
		outputs.add(CIVLConstants.showSavedStatesO);
		outputs.add(CIVLConstants.showStatesO);
		outputs.add(CIVLConstants.showTransitionsO);
		outputs.add(CIVLConstants.simplifyO);
		outputs.add(CIVLConstants.solveO);
		outputs.add(CIVLConstants.statelessPrintfO);
		outputs.add(CIVLConstants.svcompO);
		outputs.add(CIVLConstants.sysIncludePathO);
		outputs.add(CIVLConstants.traceO);
		outputs.add(CIVLConstants.userIncludePathO);
		outputs.add(CIVLConstants.verboseO);
		outputs.add(CIVLConstants.ompNoSimplifyO);
		outputs.add(CIVLConstants.webO);
		outputs.add(CIVLConstants.showTimeO);
		return outputs.toArray(new Option[numOpts]);
	}
}
