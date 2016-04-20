package edu.udel.cis.vsl.civl.run;

import static edu.udel.cis.vsl.gmc.Option.OptionType.BOOLEAN;
import static edu.udel.cis.vsl.gmc.Option.OptionType.INTEGER;
import static edu.udel.cis.vsl.gmc.Option.OptionType.STRING;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.PrintStream;
import java.util.Arrays;
import java.util.Collection;
import java.util.LinkedHashMap;

import edu.udel.cis.vsl.abc.ABC;
import edu.udel.cis.vsl.abc.ABCException;
import edu.udel.cis.vsl.abc.ABCRuntimeException;
import edu.udel.cis.vsl.abc.Activator;
import edu.udel.cis.vsl.abc.preproc.IF.PreprocessorException;
import edu.udel.cis.vsl.abc.program.IF.Program;
import edu.udel.cis.vsl.abc.token.IF.TokenUtils;
import edu.udel.cis.vsl.civl.CIVL;
import edu.udel.cis.vsl.civl.err.CIVLException;
import edu.udel.cis.vsl.civl.err.CIVLInternalException;
import edu.udel.cis.vsl.civl.err.CIVLUnimplementedFeatureException;
import edu.udel.cis.vsl.civl.model.Models;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Model;
import edu.udel.cis.vsl.civl.model.IF.ModelBuilder;
import edu.udel.cis.vsl.gmc.CommandLineException;
import edu.udel.cis.vsl.gmc.CommandLineParser;
import edu.udel.cis.vsl.gmc.GMCConfiguration;
import edu.udel.cis.vsl.gmc.MisguidedExecutionException;
import edu.udel.cis.vsl.gmc.Option;
import edu.udel.cis.vsl.sarl.SARL;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;

/**
 * Basic command line and API user interface for CIVL tools.
 * 
 * @author Stephen F. Siegel
 * 
 */
public class UserInterface {

	/***************************** Static fields *****************************/

	/**
	 * A string printed before and after titles of sections of output to make
	 * them stand out among the clutter.
	 */
	public final static String bar = "===================";

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
			"ID number of trace to replay", 0);

	public final static Option inputO = Option.newMapOption("input",
			"initialize input variable KEY to VALUE");

	public final static Option maxdepthO = Option.newScalarOption("maxdepth",
			INTEGER, "bound on search depth", Integer.MAX_VALUE);

	public final static Option minO = Option.newScalarOption("min", BOOLEAN,
			"search for minimal counterexample", false);

	public final static Option mpiO = Option.newScalarOption("mpi", BOOLEAN,
			"MPI mode", false);

	public final static Option porO = Option.newScalarOption("por", STRING,
			"partial order reduction (por) choices:\n"
					+ "    std (standard por) or scp (scoped por)", "std");

	public final static Option randomO = Option.newScalarOption("random",
			BOOLEAN, "select enabled transitions randomly; default for run,\n"
					+ "    ignored for all other commands", null);

	public final static Option saveStatesO = Option.newScalarOption(
			"saveStates", BOOLEAN, "save states during depth-first search",
			true);

	public final static Option seedO = Option.newScalarOption("seed", STRING,
			"set the random seed; applies only to run", null);

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

	public final static Option showTransitionsO = Option.newScalarOption(
			"showTransitions", BOOLEAN, "print transitions", false);

	public final static Option simplifyO = Option.newScalarOption("simplify",
			BOOLEAN, "simplify states?", true);

	public final static Option solveO = Option.newScalarOption("solve",
			BOOLEAN, "try to solve for concrete counterexample", false);

	public final static Option sysIncludePathO = Option.newScalarOption(
			"sysIncludePath", STRING, "set the system include path", null);

	public final static Option traceO = Option.newScalarOption("trace", STRING,
			"filename of trace to replay", null);

	public final static Option userIncludePathO = Option.newScalarOption(
			"userIncludePath", STRING, "set the user include path", null);

	public final static Option verboseO = Option.newScalarOption("verbose",
			BOOLEAN, "verbose mode", false);

	/*************************** Instance fields *****************************/

	/**
	 * Stderr: used only if something goes wrong, like a bad command line arg,
	 * or internal exception
	 */
	private PrintStream err = System.err;

	/** Stdout: where most output is going to go, including error reports */
	private PrintStream out = System.out;

	/**
	 * The parser from the Generic Model Checking package used to parse the
	 * command line.
	 */
	private CommandLineParser parser;

	/**
	 * The time at which this instance of UserInterface was created.
	 */
	private final double startTime = System.currentTimeMillis();

	/**
	 * The symbolic universe used in this session.
	 */
	SymbolicUniverse universe = SARL.newStandardUniverse();

	/**************************** Constructors *******************************/

	public UserInterface() {
		Collection<Option> options = Arrays.asList(errorBoundO, showModelO,
				verboseO, randomO, guidedO, seedO, debugO, echoO,
				userIncludePathO, sysIncludePathO, showTransitionsO,
				showStatesO, showSavedStatesO, showQueriesO,
				showProverQueriesO, inputO, idO, traceO, minO, maxdepthO, porO,
				saveStatesO, simplifyO, solveO, enablePrintfO, mpiO);

		parser = new CommandLineParser(options);
	}

	/*************************** Private Methods *****************************/

	/**
	 * Extracts from a string the "core" part of a filename by removing any
	 * directory prefixes and removing any file suffix. For example, invoking on
	 * "users/siegel/gcd/gcd1.cvl" will return "gcd1". This is the name used to
	 * name the model and other structures; it is used in the log, to name
	 * generated files, and for error reporting.
	 * 
	 * @param filename
	 *            a filename
	 * @return the core part of that filename
	 */
	private static String coreName(String filename) {
		String result = filename;
		char sep = File.separatorChar;
		int lastSep = filename.lastIndexOf(sep);
		if (lastSep >= 0)
			result = result.substring(lastSep + 1);
		int lastDot = result.lastIndexOf('.');
		if (lastDot >= 0)
			result = result.substring(0, lastDot);

		return result;
	}

	/**
	 * Checks that number of filenames (the free arguments in the command line
	 * after the command itself) is as expected.
	 * 
	 * @param numExpected
	 *            the number of filenames expected
	 * @param config
	 *            the configuration object which specifies the free arguments
	 * @throws CommandLineException
	 *             if the number of free arguments is not equal to one plus the
	 *             number of expected filenames
	 */
	private void checkFilenames(int numExpected, GMCConfiguration config)
			throws CommandLineException {
		int numSeen = config.getNumFreeArgs() - 1;

		if (numSeen < numExpected)
			throw new CommandLineException(
					"Missing filename(s) in command line");
		if (numSeen > numExpected)
			throw new CommandLineException("Unexpected command line argument "
					+ config.getFreeArg(numExpected + 1));
	}

	private Model extractModel(PrintStream out, GMCConfiguration config,
			String filename) throws ABCException, IOException,
			CommandLineException {
		boolean parse = "parse".equals(config.getFreeArg(0));
		boolean debug = config.isTrue(debugO);
		boolean verbose = config.isTrue(verboseO);
		boolean showModel = config.isTrue(showModelO);
		ModelBuilder modelBuilder = Models.newModelBuilder(universe,
				config.isTrue(mpiO));
		Activator frontEnd = getFrontEnd(filename, config);
		Program program;
		Model model;

		if (verbose || debug) {
			// shows absolutely everything
			program = frontEnd.showTranslation(out);
		} else {
			program = frontEnd.getProgram();
			program.prune();
			program.removeSideEffects();
		}
		if (verbose || debug)
			out.println("Extracting CIVL model...");
		model = modelBuilder.buildModel(config, program, coreName(filename));
		if (verbose || debug)
			out.println(bar + " Model " + bar + "\n");
		if (showModel || verbose || debug || parse) {
			model.print(out, verbose || debug);
		}
		return model;
	}

	/**
	 * Given a colon-separated list of filenames as a single string, this splits
	 * it up and returns an array of File objects, one for each name.
	 * 
	 * @param string
	 *            null or colon-separated list of filenames
	 * @return array of File
	 */
	private File[] extractPaths(String string) {
		if (string == null)
			return new File[0];
		else {
			String[] pieces = string.split(":");
			int numPieces = pieces.length;
			File[] result = new File[numPieces];

			for (int i = 0; i < numPieces; i++)
				result[i] = new File(pieces[i]);
			return result;
		}
	}

	/**
	 * Instantiates, initializes, and returns a new compiler front end (an
	 * instance of ABC's Activator class) from the ABC compiler. The user and
	 * system include paths, if specified in the config, are used to instantiate
	 * the front end. The front end can then be used preprocess, parse, and
	 * transform the input file.
	 * 
	 * @param filename
	 *            the name of the file to be parsed
	 * @param config
	 *            the configuration parameters for this session
	 * @return the ABC Activator that can be used to parse and process the file
	 */
	private Activator getFrontEnd(String filename, GMCConfiguration config) {
		File file = new File(filename);
		File[] userIncludes = extractPaths((String) config
				.getValue(userIncludePathO));
		File[] sysIncludes = extractPaths((String) config
				.getValue(sysIncludePathO));
		Activator frontEnd = ABC.activator(file, sysIncludes, userIncludes);

		return frontEnd;
	}

	/**
	 * Applies the ABC preprocessor to the specified file, printing the result
	 * of preprocessing to the given stream.
	 * 
	 * @param out
	 *            the stream to which to print the result of preprocessing
	 * @param config
	 *            the configuration object specifying options and arguments for
	 *            this session
	 * @param filename
	 *            the name of the file to preprocess
	 * @throws PreprocessorException
	 *             if the file does not conform to the preprocessor grammar
	 */
	private void preprocess(PrintStream out, GMCConfiguration config,
			String filename) throws PreprocessorException {
		getFrontEnd(filename, config).preprocess(out);
	}

	/**
	 * Print the command and options that user has input
	 * 
	 * @param config
	 */
	private void printCommand(GMCConfiguration config) {
		int numOfArgs = config.getNumFreeArgs();
		String command = "civl ";
		Collection<Option> options = config.getOptions();
		String arg0;

		if (numOfArgs < 1)
			return;
		arg0 = config.getFreeArg(0);
		if (arg0.equalsIgnoreCase("help"))
			return;
		command = command + arg0;
		for (Option option : options) {
			Object optionValue = config.getValue(option);

			if (optionValue != null) {
				if (option.name().equalsIgnoreCase("input")) {
					@SuppressWarnings("unchecked")
					LinkedHashMap<Object, Object> hashMap = (LinkedHashMap<Object, Object>) optionValue;

					for (Object key : hashMap.keySet()) {
						command = command + " -" + option.name()
								+ key.toString() + "="
								+ hashMap.get(key).toString();
					}
				} else
					command = command + " -" + option.name() + "="
							+ optionValue.toString();
			}

		}
		if (numOfArgs > 1)
			command = command + " " + config.getFreeArg(1);
		out.println(command);
		out.flush();
	}

	/**
	 * Prints statistics after a run. The end time is marked and compared to the
	 * start time to compute total elapsed time. Other statistics are taken from
	 * the symbolic universe created in this class. The remaining statistics are
	 * provided as parameters to this method.
	 * 
	 * @param out
	 *            the stream to which to print
	 * @param maxProcs
	 *            the maximum number of processes that existed in any state
	 *            encountered
	 * @param statesSeen
	 *            the number of states seen in the run
	 * @param statesMatched
	 *            the number of states encountered which were determined to have
	 *            been seen before
	 * @param transitions
	 *            the number of transitions executed in the course of the run
	 */
	private void printStats(PrintStream out) {
		// round up time to nearest 1/100th of second...
		double time = Math
				.ceil((System.currentTimeMillis() - startTime) / 10.0) / 100.0;
		long numValidCalls = universe.numValidCalls();
		long numProverCalls = universe.numProverValidCalls();
		long memory = Runtime.getRuntime().totalMemory();

		out.println("\n" + bar + " Stats " + bar);
		out.print("   validCalls          : ");
		out.println(numValidCalls);
		out.print("   proverCalls         : ");
		out.println(numProverCalls);
		out.print("   memory (bytes)      : ");
		out.println(memory);
		out.print("   time (s)            : ");
		out.println(time);
	}

	/**
	 * Prints usage information to the given stream and flushes the stream.
	 * 
	 * @param out
	 *            stream to which to print
	 */
	private void printUsage(PrintStream out) {
		out.println("Usage: civl <command> <options> filename ...");
		out.println("Commands:");
		out.println("  verify : verify program filename");
		out.println("  run : run program filename");
		out.println("  help : print this message");
		out.println("  replay : replay trace for program filename");
		out.println("  parse : show result of preprocessing and parsing filename");
		out.println("  preprocess : show result of preprocessing filename");
		out.println("Options:");
		parser.printUsage(out);
		out.flush();
	}

	private void setToDefault(GMCConfiguration config,
			Collection<Option> options) {
		for (Option option : options)
			setToDefault(config, option);
	}

	private void setToDefault(GMCConfiguration config, Option option) {
		config.setScalarValue(option, option.defaultValue());
	}

	private boolean showShortFileNameList(GMCConfiguration config) {
		boolean parse = "parse".equals(config.getFreeArg(0));
		boolean debug = config.isTrue(debugO);
		boolean verbose = config.isTrue(verboseO);
		boolean showModel = config.isTrue(showModelO);
		boolean showSavedStates = config.isTrue(showSavedStatesO);
		boolean showStates = config.isTrue(showStatesO);
		boolean showTransitions = config.isTrue(showTransitionsO);

		if (parse || debug || verbose || showModel || showSavedStates
				|| showStates || showTransitions)
			return true;
		return false;
	}

	/*************************** Public Methods *****************************/

	public boolean runHelp(GMCConfiguration config) {
		printUsage(out);
		return true;
	}

	public boolean runParse(GMCConfiguration config)
			throws CommandLineException, ABCException, IOException {
		checkFilenames(1, config);
		extractModel(out, config, config.getFreeArg(1));
		if (showShortFileNameList(config))
			TokenUtils.printShorterFileNameMap(out);
		return true;
	}

	public boolean runPreprocess(GMCConfiguration config)
			throws CommandLineException, PreprocessorException {
		checkFilenames(1, config);
		preprocess(out, config, config.getFreeArg(1));
		return true;
	}

	public boolean runReplay(GMCConfiguration config)
			throws CommandLineException, FileNotFoundException, IOException,
			ABCException, MisguidedExecutionException {
		boolean result;
		String sourceFilename, traceFilename;
		File traceFile;
		GMCConfiguration newConfig;
		Model model;
		TracePlayer replayer;

		checkFilenames(1, config);
		sourceFilename = config.getFreeArg(1);
		traceFilename = (String) config.getValue(traceO);
		if (traceFilename == null) {
			traceFilename = coreName(sourceFilename) + "_"
					+ config.getValueOrDefault(idO) + ".trace";
			traceFile = new File(new File("CIVLREP"), traceFilename);
		} else
			traceFile = new File(traceFilename);
		newConfig = parser.newConfig();
		// get the original config and overwrite it with new options...
		parser.parse(newConfig, traceFile); // gets free args verify filename
		setToDefault(newConfig, Arrays.asList(showModelO, verboseO, debugO,
				showTransitionsO, showStatesO, showSavedStatesO, showQueriesO,
				showProverQueriesO, enablePrintfO));
		newConfig.read(config);
		model = extractModel(out, newConfig, sourceFilename);
		if (showShortFileNameList(config))
			TokenUtils.printShorterFileNameMap(out);
		replayer = TracePlayer.guidedPlayer(newConfig, model, traceFile, out);
		result = replayer.run();
		printStats(out);
		replayer.printStats();
		out.println();
		return result;
	}

	public boolean runRun(GMCConfiguration config) throws CommandLineException,
			ABCException, IOException, MisguidedExecutionException {
		boolean result;
		String filename;
		Model model;
		TracePlayer player;

		checkFilenames(1, config);
		filename = config.getFreeArg(1);
		model = extractModel(out, config, filename);
		if (showShortFileNameList(config))
			TokenUtils.printShorterFileNameMap(out);
		player = TracePlayer.randomPlayer(config, model, out);
		out.println("\nRunning random simulation with seed " + player.getSeed()
				+ " ...");
		out.flush();
		result = player.run();
		printStats(out);
		player.printStats();
		out.println();
		return result;
	}

	public boolean runVerify(GMCConfiguration config)
			throws CommandLineException, ABCException, IOException {
		boolean result;
		String filename;
		Model model;
		Verifier verifier;
		boolean showShortFileName = showShortFileNameList(config);

		checkFilenames(1, config);
		filename = config.getFreeArg(1);
		model = extractModel(out, config, filename);
		if (showShortFileName)
			TokenUtils.printShorterFileNameMap(out);
		verifier = new Verifier(config, model, out, startTime,
				showShortFileName);
		try {
			result = verifier.run();
		} catch (CIVLUnimplementedFeatureException unimplemented) {
			verifier.terminateUpdater();
			out.println();
			out.println("Error: " + unimplemented.toString());
			return false;
		} catch (Exception e) {
			verifier.terminateUpdater();
			throw e;
		}
		printStats(out);
		verifier.printStats();
		out.println();
		verifier.printResult();
		out.flush();
		return result;
	}

	/**
	 * Parses command line arguments and runs the CIVL tool(s) as specified by
	 * those arguments.
	 * 
	 * @param args
	 *            the command line arguments, e.g., {"verify", "-verbose",
	 *            "foo.c"}. This is an array of strings of length at least 1;
	 *            element 0 should be the name of the command
	 * @return true iff everything succeeded and no errors discovered
	 * @throws CommandLineException
	 *             if the args are not properly formatted commandline arguments
	 */
	public boolean runMain(String[] args) throws CommandLineException {
		GMCConfiguration config = parser.parse(Arrays.asList(args));
		int numFree = config.getNumFreeArgs();
		String command;

		out.println("CIVL v" + CIVL.version + " of " + CIVL.date
				+ " -- http://vsl.cis.udel.edu/civl");
		out.flush();
		if (config.isTrue(echoO))
			printCommand(config);
		if (numFree == 0)
			throw new CommandLineException("Missing command");
		command = config.getFreeArg(0);
		if (config.isTrue(showQueriesO))
			universe.setShowQueries(true);
		if (config.isTrue(showProverQueriesO))
			universe.setShowProverQueries(true);
		try {
			switch (command) {
			case "help":
				return runHelp(config);
			case "verify":
				return runVerify(config);
			case "replay":
				return runReplay(config);
			case "run":
				return runRun(config);
			case "parse":
				return runParse(config);
			case "preprocess":
				return runPreprocess(config);
			default:
				throw new CommandLineException("Unknown command: " + command);
			}
		} catch (ABCException e) {
			err.println(e);
		} catch (ABCRuntimeException e) {
			err.println(e);
		} catch (IOException e) {
			err.println(e);
		} catch (MisguidedExecutionException e) {
			// this is almost definitely a bug, so throw it:
			throw new CIVLInternalException("Error in replay: "
					+ e.getMessage(), (CIVLSource) null);
		} catch (CIVLInternalException e) {
			// Something went wrong, report with full stack trace.
			throw e;
		} catch (CIVLException e) {
			err.println(e);
		}
		err.flush();
		return false;
	}

	/**
	 * Runs the appropriate CIVL tools based on the command line arguments.
	 * 
	 * @param args
	 *            command line arguments
	 * @return true iff everything succeeded and no errors were found
	 */
	public boolean run(String... args) {
		try {
			return runMain(args);
		} catch (CommandLineException e) {
			err.println(e.getMessage());
			err.println("Type \"civl help\" for command line syntax.");
			err.flush();
		}
		return false;
	}

	/**
	 * Runs the appropriate CIVL tools based on the command line arguments. This
	 * variant provided in case a collection is more convenient than an array.
	 * 
	 * @param args
	 *            command line arguments as collection
	 * @return true iff everything succeeeded and no errors were found
	 */
	public boolean run(Collection<String> args) {
		return run(args.toArray(new String[args.size()]));
	}

	/**
	 * Runs command specified as one big String.
	 * 
	 * @param argsString
	 * @return
	 */
	public boolean run(String argsString) {
		String[] args = argsString.split(" ");

		return run(args);
	}
}
