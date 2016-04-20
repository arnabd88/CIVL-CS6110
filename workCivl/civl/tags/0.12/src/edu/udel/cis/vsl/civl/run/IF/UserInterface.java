package edu.udel.cis.vsl.civl.run.IF;

import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.bar;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.date;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.deadlockO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.debugO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.echoO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.enablePrintfO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.errorBoundO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.guiO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.guidedO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.idO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.inputO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.maxdepthO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.minO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.randomO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.saveStatesO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.seedO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.showAmpleSetO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.showAmpleSetWtStatesO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.showInputVarsO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.showModelO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.showPathConditionO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.showProgramO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.showProverQueriesO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.showQueriesO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.showSavedStatesO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.showStatesO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.showTransitionsO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.simplifyO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.solveO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.statelessPrintfO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.svcompO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.sysIncludePathO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.traceO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.userIncludePathO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.verboseO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.version;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Set;

import edu.udel.cis.vsl.abc.ABC;
import edu.udel.cis.vsl.abc.Activator;
import edu.udel.cis.vsl.abc.ast.IF.AST;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode.NodeKind;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.VariableDeclarationNode;
import edu.udel.cis.vsl.abc.config.IF.Configuration.Language;
import edu.udel.cis.vsl.abc.err.IF.ABCException;
import edu.udel.cis.vsl.abc.err.IF.ABCRuntimeException;
import edu.udel.cis.vsl.abc.preproc.IF.Preprocessor;
import edu.udel.cis.vsl.abc.preproc.IF.PreprocessorException;
import edu.udel.cis.vsl.abc.program.IF.Program;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;
import edu.udel.cis.vsl.abc.transform.IF.Combiner;
import edu.udel.cis.vsl.abc.transform.IF.Transform;
import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.gui.IF.CIVL_GUI;
import edu.udel.cis.vsl.civl.gui.IF.GUIs;
import edu.udel.cis.vsl.civl.model.IF.CIVLException;
import edu.udel.cis.vsl.civl.model.IF.CIVLInternalException;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.CIVLSyntaxException;
import edu.udel.cis.vsl.civl.model.IF.CIVLUnimplementedFeatureException;
import edu.udel.cis.vsl.civl.model.IF.Model;
import edu.udel.cis.vsl.civl.model.IF.ModelBuilder;
import edu.udel.cis.vsl.civl.model.IF.Models;
import edu.udel.cis.vsl.civl.semantics.IF.Transition;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.transform.IF.CIVLTransform;
import edu.udel.cis.vsl.civl.util.IF.Pair;
import edu.udel.cis.vsl.gmc.CommandLineException;
import edu.udel.cis.vsl.gmc.CommandLineParser;
import edu.udel.cis.vsl.gmc.GMCConfiguration;
import edu.udel.cis.vsl.gmc.MisguidedExecutionException;
import edu.udel.cis.vsl.gmc.Option;
import edu.udel.cis.vsl.gmc.Trace;
import edu.udel.cis.vsl.sarl.SARL;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;

/**
 * Basic command line and API user interface for CIVL tools.
 * 
 * @author Stephen F. Siegel
 * 
 */
public class UserInterface {

	/* ************************* Instance fields *************************** */

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

	/* ************************** Constructors ***************************** */

	public UserInterface() {
		Collection<Option> options = Arrays.asList(errorBoundO, showModelO,
				verboseO, randomO, guidedO, seedO, debugO, echoO,
				userIncludePathO, sysIncludePathO, showTransitionsO,
				showStatesO, showSavedStatesO, showQueriesO,
				showProverQueriesO, inputO, idO, traceO, minO, maxdepthO,
				saveStatesO, simplifyO, solveO, enablePrintfO, showAmpleSetO,
				showAmpleSetWtStatesO, statelessPrintfO, guiO, deadlockO,
				svcompO, showInputVarsO, showProgramO, showPathConditionO);

		parser = new CommandLineParser(options);
	}

	/* ************************* Private Methods *************************** */

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

	private Pair<Model, Preprocessor> extractModel(PrintStream out,
			GMCConfiguration config, String filename, SymbolicUniverse universe)
			throws ABCException, IOException, CommandLineException {
		return extractModel(out, config, filename,
				Models.newModelBuilder(universe));
	}

	private Pair<Model, Preprocessor> extractModel(PrintStream out,
			GMCConfiguration config, String filename, ModelBuilder modelBuilder)
			throws ABCException, IOException, CommandLineException {
		CIVLConfiguration civlConfig = new CIVLConfiguration(config);
		boolean parse = "parse".equals(config.getFreeArg(0));
		boolean debug = civlConfig.debug();
		boolean verbose = civlConfig.verbose();
		boolean showModel = config.isTrue(showModelO);
		Activator frontEnd = getFrontEnd(filename, config);
		Program program;
		Model model;
		Preprocessor preprocessor = frontEnd.getPreprocessor();
		List<String> inputVars = getInputVariables(config);
		boolean hasFscanf = false;

		try {
			if (verbose || debug) {
				// shows absolutely everything
				program = frontEnd.showTranslation(out);
			} else {
				program = frontEnd.getProgram();
			}
			applyTransformers(filename, program, preprocessor, civlConfig,
					frontEnd, inputVars);
			if (civlConfig.showProgram() && !civlConfig.debugOrVerbose())
				CIVLTransform.printProgram2CIVL(out, program);
			hasFscanf = CIVLTransform.hasFunctionCalls(program.getAST(),
					Arrays.asList("scanf", "fscanf"));
			if (config.isTrue(showInputVarsO) || verbose || debug) {
				List<String> inputVarNames = inputVariableNames(program
						.getAST());

				if (inputVarNames.size() < 1)
					out.println("No input variables are declared for this program.");
				else {
					out.println("This program has declared "
							+ inputVarNames.size() + " input variables:");
					for (String name : inputVarNames) {
						out.print(name + " ");
					}
					out.println();
				}
			}
			if (verbose || debug)
				out.println("Extracting CIVL model...");
			model = modelBuilder.buildModel(config, program,
					coreName(filename), debug, out);
			model.setHasFscanf(hasFscanf);
			if (verbose || debug)
				out.println(bar + " Model " + bar + "\n");
			if (showModel || verbose || debug || parse) {
				model.print(out, verbose || debug);
			}
			return new Pair<>(model, preprocessor);
		} catch (CIVLException ex) {
			err.println(ex);
			preprocessor.printShorterFileNameMap(err);
		}
		return null;
	}

	private List<String> getInputVariables(GMCConfiguration config) {
		Collection<Option> options = config.getOptions();
		List<String> inputVars = new ArrayList<>();

		for (Option option : options) {
			Object optionValue = config.getValue(option);

			if (optionValue != null) {
				if (option.name().equals("input")) {
					@SuppressWarnings("unchecked")
					LinkedHashMap<Object, Object> hashMap = (LinkedHashMap<Object, Object>) optionValue;

					for (Object key : hashMap.keySet()) {
						inputVars.add(key.toString());
					}
				}
			}
		}
		return inputVars;
	}

	/**
	 * Apply transformers of the program.
	 * 
	 * @param fileName
	 * @param program
	 * @throws SyntaxException
	 */
	private void applyTransformers(String fileName, Program program,
			Preprocessor preprocessor, CIVLConfiguration config,
			Activator frontEnd, List<String> inputVars) throws SyntaxException {
		Set<String> headers = preprocessor.headerFiles();
		boolean isC = fileName.endsWith(".c");
		boolean hasCIVLPragma = false, hasStdio = false, hasOmp = false, hasMpi = false, hasPthread = false;

		hasCIVLPragma = CIVLTransform.hasCIVLPragma(program.getAST());
		if (headers.contains("stdio.h"))
			hasStdio = true;
		if (isC && (headers.contains("omp.h") || program.hasOmpPragma()))
			hasOmp = true;
		if (isC && headers.contains("pthread.h"))
			hasPthread = true;
		if (isC && headers.contains("mpi.h"))
			hasMpi = true;
		// always apply general transformation.
		if (config.debugOrVerbose())
			this.out.println("Apply general transformer...");
		CIVLTransform.applyTransformer(program, CIVLTransform.GENERAL,
				inputVars, frontEnd.getASTBuilder(), config);
		if (config.debugOrVerbose()) {
			frontEnd.printProgram(out, program);
			CIVLTransform.printProgram2CIVL(out, program);
		}
		if (hasCIVLPragma) {
			if (config.debugOrVerbose())
				this.out.println("Apply CIVL pragma transformer...");
			CIVLTransform.applyTransformer(program, CIVLTransform.CIVL_PRAGMA,
					inputVars, frontEnd.getASTBuilder(), config);
			if (config.debugOrVerbose()) {
				frontEnd.printProgram(out, program);
				CIVLTransform.printProgram2CIVL(out, program);
			}
		}
		if (hasStdio) {
			if (config.debugOrVerbose())
				this.out.println("Apply IO transformer...");
			CIVLTransform.applyTransformer(program, CIVLTransform.IO,
					inputVars, frontEnd.getASTBuilder(), config);
			if (config.debugOrVerbose()) {
				frontEnd.printProgram(out, program);
				CIVLTransform.printProgram2CIVL(out, program);
			}
		}
		if (hasOmp) {
			if (config.debugOrVerbose())
				this.out.println("Apply OpenMP parser...");
			CIVLTransform.applyTransformer(program, CIVLTransform.OMP_PRAGMA,
					inputVars, frontEnd.getASTBuilder(), config);
			if (config.debugOrVerbose())
				frontEnd.printProgram(out, program);
			if (config.debugOrVerbose())
				this.out.println("Apply OpenMP transformer...");
			CIVLTransform.applyTransformer(program, CIVLTransform.OMP_SIMPLIFY,
					inputVars, frontEnd.getASTBuilder(), config);
			if (config.debugOrVerbose()) {
				frontEnd.printProgram(out, program);
				CIVLTransform.printProgram2CIVL(out, program);
			}
		}
		if (hasPthread) {
			if (config.debugOrVerbose())
				this.out.println("Apply Pthread transformer...");
			CIVLTransform.applyTransformer(program, CIVLTransform.PTHREAD,
					inputVars, frontEnd.getASTBuilder(), config);
			if (config.debugOrVerbose()) {
				frontEnd.printProgram(out, program);
				CIVLTransform.printProgram2CIVL(out, program);
			}
		}
		if (hasMpi) {
			if (config.debugOrVerbose())
				this.out.println("Apply MPI transformer...");
			CIVLTransform.applyTransformer(program, CIVLTransform.MPI,
					inputVars, frontEnd.getASTBuilder(), config);
			if (config.debugOrVerbose()) {
				frontEnd.printProgram(out, program);
				CIVLTransform.printProgram2CIVL(out, program);
			}
		}
		// always apply pruner and side effect remover
		if (config.debugOrVerbose())
			this.out.println("Apply pruner...");
		program.applyTransformer("prune");
		if (config.debugOrVerbose()) {
			frontEnd.printProgram(out, program);
			CIVLTransform.printProgram2CIVL(out, program);
		}
		if (config.debugOrVerbose())
			this.out.println("Apply side-effect remover...");
		program.applyTransformer("sef");
		if (config.debugOrVerbose()) {
			frontEnd.printProgram(out, program);
			CIVLTransform.printProgram2CIVL(out, program);
		}
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
		File civlDefaultInclude = new File(new File(".").getAbsoluteFile(),
				"text/include");
		boolean hasCIVLDefaultSet = false;
		String civlDefaultIncludePath = civlDefaultInclude.getAbsolutePath();
		Activator frontEnd;

		for (File sysInclude : sysIncludes) {
			if (sysInclude.getAbsolutePath().equals(civlDefaultIncludePath))
				hasCIVLDefaultSet = true;
		}
		if (!hasCIVLDefaultSet) {
			int length = sysIncludes.length;
			List<File> newSysIncludes = new ArrayList<>(length + 1);

			for (int i = 0; i < length; i++) {
				newSysIncludes.add(sysIncludes[i]);
			}
			newSysIncludes.add(civlDefaultInclude);
			sysIncludes = new File[length + 1];
			newSysIncludes.toArray(sysIncludes);
		}
		frontEnd = ABC.activator(file, sysIncludes, userIncludes,
				Language.CIVL_C);

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
				if (option.name().equals("input")) {
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
	private void printStats(PrintStream out, SymbolicUniverse universe) {
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
		out.println("  gui : launch civl in gui mode (beta)");
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

	private List<String> inputVariableNames(AST ast) {
		ASTNode root = ast.getRootNode();
		List<String> variableNames = new ArrayList<>();

		for (ASTNode child : root.children()) {
			if (child != null
					&& child.nodeKind() == NodeKind.VARIABLE_DECLARATION) {
				VariableDeclarationNode variable = (VariableDeclarationNode) child;

				if (variable.getTypeNode().isInputQualified())
					variableNames.add(variable.getName());
			}
		}
		return variableNames;
	}

	/* ************************** Public Methods *************************** */

	public boolean runHelp(GMCConfiguration config) {
		printUsage(out);
		return true;
	}

	public boolean runParse(GMCConfiguration config)
			throws CommandLineException, ABCException, IOException {
		SymbolicUniverse universe = SARL.newStandardUniverse();
		Preprocessor preprocessor;
		Pair<Model, Preprocessor> result;

		checkFilenames(1, config);
		result = extractModel(out, config, config.getFreeArg(1), universe);
		if (result == null)
			return false;
		preprocessor = result.right;
		if (showShortFileNameList(config))
			preprocessor.printShorterFileNameMap(out);
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
		SymbolicUniverse universe = SARL.newStandardUniverse();
		boolean result;
		String sourceFilename, traceFilename;
		File traceFile;
		GMCConfiguration newConfig;
		Model model;
		TracePlayer replayer;
		boolean guiMode = config.isTrue(guiO);
		Pair<Model, Preprocessor> modelAndPreprocessor;
		Preprocessor preprocessor;
		Trace<Transition, State> trace;

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
				showStatesO, showSavedStatesO, showQueriesO,
				showProverQueriesO, enablePrintfO, statelessPrintfO));
		newConfig.setScalarValue(showTransitionsO, true);
		newConfig.read(config);
		if (newConfig.isTrue(showProverQueriesO))
			universe.setShowProverQueries(true);
		if (newConfig.isTrue(showQueriesO))
			universe.setShowQueries(true);
		modelAndPreprocessor = extractModel(out, newConfig, sourceFilename,
				universe);
		model = modelAndPreprocessor.left;
		preprocessor = modelAndPreprocessor.right;
		replayer = TracePlayer.guidedPlayer(newConfig, model, traceFile, out,
				err, preprocessor);
		trace = replayer.run();
		result = trace.result();
		if (guiMode) {
			@SuppressWarnings("unused")
			CIVL_GUI gui = new CIVL_GUI(trace, replayer.symbolicUtil);
		}
		printStats(out, universe);
		replayer.printStats();
		out.println();
		preprocessor.printShorterFileNameMap(out);
		return result;
	}

	public boolean runRun(GMCConfiguration config) throws CommandLineException,
			ABCException, IOException, MisguidedExecutionException {
		SymbolicUniverse universe = SARL.newStandardUniverse();
		boolean result;
		String filename;
		Model model;
		TracePlayer player;
		Pair<Model, Preprocessor> modelAndPreprocessor;
		Preprocessor preprocessor;

		if (config.isTrue(showProverQueriesO))
			universe.setShowProverQueries(true);
		if (config.isTrue(showQueriesO))
			universe.setShowQueries(true);
		checkFilenames(1, config);
		filename = config.getFreeArg(1);
		modelAndPreprocessor = extractModel(out, config, filename, universe);
		model = modelAndPreprocessor.left;
		preprocessor = modelAndPreprocessor.right;
		if (showShortFileNameList(config))
			preprocessor.printShorterFileNameMap(out);
		config.setScalarValue(showTransitionsO, true);
		player = TracePlayer
				.randomPlayer(config, model, out, err, preprocessor);
		out.println("\nRunning random simulation with seed " + player.getSeed()
				+ " ...");
		out.flush();
		result = player.run().result();
		printStats(out, universe);
		player.printStats();
		out.println();
		return result;
	}

	public boolean runVerify(GMCConfiguration config)
			throws CommandLineException, ABCException, IOException {
		SymbolicUniverse universe = SARL.newStandardUniverse();
		boolean result;
		String filename;
		Model model;
		Verifier verifier;
		boolean showShortFileName = showShortFileNameList(config);
		Pair<Model, Preprocessor> modelAndPreprocessor;
		Preprocessor preprocessor;

		if (config.isTrue(showProverQueriesO))
			universe.setShowProverQueries(true);
		if (config.isTrue(showQueriesO))
			universe.setShowQueries(true);
		checkFilenames(1, config);
		filename = config.getFreeArg(1);
		modelAndPreprocessor = extractModel(out, config, filename, universe);
		if (modelAndPreprocessor == null)
			return false;
		model = modelAndPreprocessor.left;
		preprocessor = modelAndPreprocessor.right;
		if (showShortFileName)
			preprocessor.printShorterFileNameMap(out);
		verifier = new Verifier(config, model, out, err, startTime,
				showShortFileName, preprocessor);
		try {
			result = verifier.run();
		} catch (CIVLUnimplementedFeatureException unimplemented) {
			verifier.terminateUpdater();
			out.println();
			out.println("Error: " + unimplemented.toString());
			preprocessor.printShorterFileNameMap(out);
			return false;
		} catch (CIVLSyntaxException syntax) {
			verifier.terminateUpdater();
			err.println(syntax);
			preprocessor.printShorterFileNameMap(err);
			return false;
		} catch (Exception e) {
			verifier.terminateUpdater();
			throw e;
		}
		printStats(out, universe);
		verifier.printStats();
		out.println();
		verifier.printResult();
		out.flush();
		return result;
	}

	public boolean runCompare(GMCConfiguration config)
			throws CommandLineException, ABCException, IOException {
		SymbolicUniverse universe = SARL.newStandardUniverse();
		boolean result = false;
		String filename0, filename1;
		Program program0, program1, compositeProgram;
		Combiner combiner = Transform.newCompareCombiner();
		Model model;
		Verifier verifier;
		boolean showShortFileName = showShortFileNameList(config);
		boolean showProgram = config.isTrue(showProgramO);
		boolean debug = config.isTrue(debugO);
		boolean verbose = config.isTrue(verboseO);
		boolean showModel = config.isTrue(showModelO);
		Activator frontEnd0, frontEnd1;
		boolean parse = "parse".equals(config.getFreeArg(0));
		ModelBuilder modelBuilder = Models.newModelBuilder(universe);
		Preprocessor preprocessor0;
		Preprocessor preprocessor1;
		List<String> inputVars = getInputVariables(config);
		CIVLConfiguration civlConfig = new CIVLConfiguration(config);

		checkFilenames(2, config);
		filename0 = config.getFreeArg(1);
		filename1 = config.getFreeArg(2);
		frontEnd0 = getFrontEnd(filename0, config);
		frontEnd1 = getFrontEnd(filename1, config);
		preprocessor0 = frontEnd0.getPreprocessor();
		preprocessor1 = frontEnd1.getPreprocessor();

		if (verbose || debug) {
			// shows absolutely everything
			program0 = frontEnd0.showTranslation(out);
			program1 = frontEnd1.showTranslation(out);
		} else {
			program0 = frontEnd0.getProgram();

			applyTransformers(filename0, program0, preprocessor0, civlConfig,
					frontEnd0, inputVars);
			program1 = frontEnd1.getProgram();
			applyTransformers(filename1, program1, preprocessor1, civlConfig,
					frontEnd1, inputVars);
		}
		if (verbose || debug)
			out.println("Generating composite program...");
		compositeProgram = frontEnd0.getProgramFactory().newProgram(
				combiner.combine(program0.getAST(), program1.getAST()));
		if (verbose || debug) {
			compositeProgram.print(out);
			CIVLTransform.printProgram2CIVL(out, compositeProgram);
		}
		if (showProgram && !(verbose || debug))
			CIVLTransform.printProgram2CIVL(out, compositeProgram);
		if (config.isTrue(showInputVarsO) || verbose || debug) {
			List<String> inputVarNames = inputVariableNames(compositeProgram
					.getAST());

			if (inputVarNames.size() < 1)
				out.println("No input variables are declared for either program.");
			else {
				out.println("This composited program has declared "
						+ inputVarNames.size() + " input variables:");
				for (String name : inputVarNames) {
					out.print(name + " ");
				}
				out.println();
			}
		}
		if (showShortFileName) {
			preprocessor0.printShorterFileNameMap(out);
			preprocessor1.printShorterFileNameMap(out);
		}

		if (verbose || debug)
			out.println("Extracting CIVL model...");
		model = modelBuilder.buildModel(config, compositeProgram,
				"Composite of " + coreName(filename0) + " and "
						+ coreName(filename1), debug, out);
		if (verbose || debug)
			out.println(bar + " Model " + bar + "\n");
		if (showModel || verbose || debug || parse) {
			model.print(out, verbose || debug);
		}
		verifier = new Verifier(config, model, out, err, startTime,
				showShortFileName, preprocessor0);
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
		printStats(out, universe);
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
		SymbolicUniverse universe = SARL.newStandardUniverse();
		String command;

		out.println("CIVL v" + version + " of " + date
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
			case "compare":
				return runCompare(config);
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
			case "gui":
				return runGui();
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

	private boolean runGui() {
		GUIs.startGUI();
		return true;
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
	 * @return true iff everything succeeded and no errors were found
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
