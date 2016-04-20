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
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.ompNoSimplifyO;
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
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Set;
import java.util.Stack;

import edu.udel.cis.vsl.abc.FrontEnd;
import edu.udel.cis.vsl.abc.ast.IF.AST;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode.NodeKind;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.VariableDeclarationNode;
import edu.udel.cis.vsl.abc.config.IF.Configuration.Language;
import edu.udel.cis.vsl.abc.err.IF.ABCException;
import edu.udel.cis.vsl.abc.err.IF.ABCRuntimeException;
import edu.udel.cis.vsl.abc.parse.IF.ParseException;
import edu.udel.cis.vsl.abc.preproc.IF.Preprocessor;
import edu.udel.cis.vsl.abc.preproc.IF.PreprocessorException;
import edu.udel.cis.vsl.abc.program.IF.Program;
import edu.udel.cis.vsl.abc.token.IF.CTokenSource;
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

	/**
	 * The ABC front end.
	 */
	private FrontEnd frontEnd = new FrontEnd();

	/* ************************** Constructors ***************************** */

	public UserInterface() {
		Collection<Option> options = Arrays.asList(errorBoundO, showModelO,
				verboseO, randomO, guidedO, seedO, debugO, echoO,
				userIncludePathO, sysIncludePathO, showTransitionsO,
				showStatesO, showSavedStatesO, showQueriesO,
				showProverQueriesO, inputO, idO, traceO, minO, maxdepthO,
				saveStatesO, simplifyO, solveO, enablePrintfO, showAmpleSetO,
				showAmpleSetWtStatesO, statelessPrintfO, guiO, deadlockO,
				svcompO, showInputVarsO, showProgramO, showPathConditionO,
				ompNoSimplifyO);

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

	/**
	 * Gets default implementation of CIVL's libraries and compile them to ASTs,
	 * greedily.
	 * 
	 * @param preprocessor
	 *            the preprocessor for preprocessing tokens.
	 * @param config
	 *            the command line
	 * @return
	 * @throws PreprocessorException
	 * @throws SyntaxException
	 * @throws ParseException
	 * @throws IOException
	 */
	private List<AST> asts2Link(Preprocessor preprocessor)
			throws PreprocessorException, SyntaxException, ParseException,
			IOException {
		List<AST> ASTs = new ArrayList<>();
		Set<String> checkedHeaderFiles = new HashSet<>();
		Stack<String> headerFiles = new Stack<>();

		for (String header : preprocessor.headerFiles())
			headerFiles.push(header);
		while (!headerFiles.isEmpty()) {
			String header = headerFiles.pop();

			checkedHeaderFiles.add(header);
			if (header.equals("string.h"))
				ASTs.add(this.compileFile(preprocessor, "string.cvl"));
			else if (header.equals("civlc.cvh"))
				ASTs.add(this.compileFile(preprocessor, "civlc.cvl"));
			else if (header.equals("civlmpi.cvh"))
				ASTs.add(this.compileFile(preprocessor, "civlmpi.cvl"));
			else if (header.equals("mpi.h"))
				ASTs.add(this.compileFile(preprocessor, "mpi.cvl"));
			else if (header.equals("comm.cvh"))
				ASTs.add(this.compileFile(preprocessor, "comm.cvl"));
			else if (header.equals("concurrency.cvh"))
				ASTs.add(this.compileFile(preprocessor, "concurrency.cvl"));
			for (String newHeader : preprocessor.headerFiles()) {
				if (!headerFiles.contains(newHeader)
						&& !checkedHeaderFiles.contains(newHeader))
					headerFiles.push(newHeader);
			}
		}
		return ASTs;
	}

	private AST compileFile(Preprocessor preprocessor, File file)
			throws SyntaxException, ParseException, PreprocessorException {
		CTokenSource tokens = preprocessor.outputTokenSource(file);

		return frontEnd.getASTBuilder().getTranslationUnit(
				frontEnd.getParser().parse(tokens));
	}

	private AST compileFile(Preprocessor preprocessor, String filename)
			throws SyntaxException, ParseException, PreprocessorException,
			IOException {
		CTokenSource tokens = preprocessor.outputTokenSource(filename);

		return frontEnd.getASTBuilder().getTranslationUnit(
				frontEnd.getParser().parse(tokens));
	}

	private Program compileLinkAndTransform(Preprocessor preprocessor,
			String filename, GMCConfiguration config,
			CIVLConfiguration civlConfig) throws PreprocessorException,
			SyntaxException, ParseException, IOException {
		File file = new File(filename);
		AST userAST = this.compileFile(preprocessor, file);
		Program program;

		program = this.link(preprocessor, userAST);
		if (civlConfig.debugOrVerbose())
			program.prettyPrint(out);
		applyAllTransformers(filename, preprocessor, program, civlConfig);
		return program;
	}

	private Program link(Preprocessor preprocessor, AST userAST)
			throws PreprocessorException, SyntaxException, ParseException,
			IOException {
		ArrayList<AST> asts = new ArrayList<>();
		AST[] TUs;

		asts.addAll(this.asts2Link(preprocessor));
		asts.add(userAST);
		TUs = new AST[asts.size()];
		asts.toArray(TUs);
		return frontEnd.link(TUs, Language.CIVL_C);
	}

	private Pair<Model, Preprocessor> extractModel(PrintStream out,
			GMCConfiguration config, String filename, ModelBuilder modelBuilder)
			throws ABCException, IOException, CommandLineException {
		CIVLConfiguration civlConfig = new CIVLConfiguration(config);
		boolean parse = "parse".equals(config.getFreeArg(0));
		boolean debug = civlConfig.debug();
		boolean verbose = civlConfig.verbose();
		boolean showModel = config.isTrue(showModelO);
		Preprocessor preprocessor = frontEnd.getPreprocessor(
				this.getSysIncludes(config), this.getUserIncludes(config));
		Model model;
		boolean hasFscanf = false;
		Program program;

		try {
			program = this.compileLinkAndTransform(preprocessor, filename,
					config, civlConfig);
			if (civlConfig.showProgram() && !civlConfig.debugOrVerbose())
				program.prettyPrint(out);
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

	@SuppressWarnings("unused")
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
	private void applyAllTransformers(String fileName,
			Preprocessor preprocessor, Program program, CIVLConfiguration config)
			throws SyntaxException {
		this.applyTranslationTransformers(fileName, preprocessor, program,
				config);
		this.applyDefaultTransformers(program, config);
	}

	private void applyTranslationTransformers(String fileName,
			Preprocessor preprocessor, Program program, CIVLConfiguration config)
			throws SyntaxException {
		Set<String> headers = preprocessor.headerFiles();
		boolean isC = fileName.endsWith(".c");
		boolean hasStdio = false, hasOmp = false, hasMpi = false, hasPthread = false;

		new CIVLTransform();
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
		program.applyTransformer(CIVLTransform.GENERAL);
		if (config.debugOrVerbose()) {
			program.prettyPrint(out);
		}
		if (hasStdio) {
			if (config.debugOrVerbose())
				this.out.println("Apply IO transformer...");
			program.applyTransformer(CIVLTransform.IO);
			if (config.debugOrVerbose()) {
				program.prettyPrint(out);
			}
		}
		if (hasOmp) {
			if (!config.ompNoSimplify()) {
				if (config.debugOrVerbose())
					this.out.println("Apply OpenMP simplifier...");
				program.applyTransformer(CIVLTransform.OMP_SIMPLIFY);
			}
			if (config.debugOrVerbose())
				this.out.println("Apply OpenMP transformer...");
			program.applyTransformer(CIVLTransform.OPENMP);
			if (config.debugOrVerbose())
				program.prettyPrint(out);
		}
		if (hasPthread) {
			if (config.svcomp()) {
				if (config.debugOrVerbose())
					this.out.println("Apply Macro transformer for svcomp programs ...");
				program.applyTransformer(CIVLTransform.MACRO);
				if (config.debugOrVerbose())
					program.prettyPrint(out);
			}
			if (config.debugOrVerbose())
				this.out.println("Apply Pthread transformer...");
			program.applyTransformer(CIVLTransform.PTHREAD);
			if (config.debugOrVerbose())
				program.prettyPrint(out);
		}
		if (hasMpi) {
			if (config.debugOrVerbose())
				this.out.println("Apply MPI transformer...");
			program.applyTransformer(CIVLTransform.MPI);
			if (config.debugOrVerbose())
				program.prettyPrint(out);
		}
	}

	private void applyDefaultTransformers(Program program,
			CIVLConfiguration config) throws SyntaxException {
		// always apply pruner and side effect remover
		if (config.debugOrVerbose())
			this.out.println("Apply pruner...");
		program.applyTransformer("prune");
		if (config.debugOrVerbose())
			program.prettyPrint(out);
		if (config.debugOrVerbose())
			this.out.println("Apply side-effect remover...");
		program.applyTransformer("sef");
		if (config.debugOrVerbose())
			program.prettyPrint(out);
	}

	private File[] getUserIncludes(GMCConfiguration config) {
		return extractPaths((String) config.getValue(userIncludePathO));
	}

	private File[] getSysIncludes(GMCConfiguration config) {
		File[] sysIncludes = extractPaths((String) config
				.getValue(sysIncludePathO));
		File civlDefaultInclude = new File(new File(".").getAbsoluteFile(),
				"text/include");
		boolean hasCIVLDefaultSet = false;
		String civlDefaultIncludePath = civlDefaultInclude.getAbsolutePath();

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
		return sysIncludes;
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
		Preprocessor preprocessor = frontEnd.getPreprocessor(
				this.getSysIncludes(config), this.getUserIncludes(config));

		preprocessor.printOutput(out, new File(filename));
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
		Pair<Model, Preprocessor> modelResult;

		checkFilenames(1, config);
		modelResult = extractModel(out, config, config.getFreeArg(1), universe);
		if (modelResult == null)
			return false;
		if (showShortFileNameList(config))
			modelResult.right.printShorterFileNameMap(out);
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
		Pair<Model, Preprocessor> modelResult;
		Model model;
		TracePlayer replayer;
		boolean guiMode = config.isTrue(guiO);
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
		modelResult = extractModel(out, newConfig, sourceFilename, universe);
		if (modelResult == null)
			return false;
		model = modelResult.left;
		preprocessor = modelResult.right;
		replayer = TracePlayer.guidedPlayer(newConfig, model, traceFile, out,
				err, preprocessor);
		trace = replayer.run();
		result = trace.result();
		if (guiMode) {
			@SuppressWarnings("unused")
			CIVL_GUI gui = new CIVL_GUI(trace, replayer.symbolicAnalyzer);
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
		Combiner combiner = Transform.compareCombiner();
		Model model;
		Verifier verifier;
		boolean showShortFileName = showShortFileNameList(config);
		boolean showProgram = config.isTrue(showProgramO);
		boolean debug = config.isTrue(debugO);
		boolean verbose = config.isTrue(verboseO);
		boolean showModel = config.isTrue(showModelO);
		boolean parse = "parse".equals(config.getFreeArg(0));
		ModelBuilder modelBuilder = Models.newModelBuilder(universe);
		Preprocessor preprocessor0;
		Preprocessor preprocessor1;
		CIVLConfiguration civlConfig = new CIVLConfiguration(config);
		@SuppressWarnings("unused")
		AST ast0, combinedAST, pointerAST;

		checkFilenames(2, config);
		filename0 = config.getFreeArg(1);
		filename1 = config.getFreeArg(2);
		preprocessor0 = frontEnd.getPreprocessor(this.getSysIncludes(config),
				this.getUserIncludes(config));
		preprocessor1 = frontEnd.getPreprocessor(this.getSysIncludes(config),
				this.getUserIncludes(config));
		// ast0 = this.compileFile(preprocessor0, new File(filename0));
		// if (!preprocessor0.headerFiles().contains("pointer.cvh")) {
		// pointerAST = this.compileFile(preprocessor0, new File(
		// "../abc/text/include/pointer.cvh"));
		// ast0 = frontEnd.link(new AST[] { pointerAST, ast0 },
		// Language.CIVL_C).getAST();
		// program0 = this.link(preprocessor0, ast0);
		// } else
		// program0 = frontEnd.link(new AST[] { ast0 }, Language.CIVL_C);
		// this.applyTranslationTransformers(filename0, preprocessor0, program0,
		// civlConfig);
		program0 = this.compileLinkAndTransform(preprocessor0, filename0,
				config, civlConfig);
		program1 = this.compileLinkAndTransform(preprocessor1, filename1,
				config, civlConfig);
		if (verbose || debug)
			out.println("Generating composite program...");
		combinedAST = combiner.combine(program0.getAST(), program1.getAST());
		compositeProgram = frontEnd.getProgramFactory(
				frontEnd.getStandardAnalyzer(Language.CIVL_C)).newProgram(
				combinedAST);
		// this.applyDefaultTransformers(compositeProgram, civlConfig);
		if (showProgram || verbose || debug) {
			compositeProgram.prettyPrint(out);
		}
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
				showShortFileName, preprocessor1);
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

	// private Set<String> getHeaderFiles(AST ast) {
	// Set<String> headerFiles = new HashSet<>();
	//
	// getHeaderFiles(ast.getRootNode(), headerFiles);
	// return headerFiles;
	// }
	//
	// private void getHeaderFiles(ASTNode node, Set<String> result) {
	// String mySource = node.getSource().getFirstToken().getSourceFile()
	// .getName();
	//
	// if (!result.contains(mySource))
	// result.add(mySource);
	// for (ASTNode child : node.children()) {
	// if (child != null)
	// getHeaderFiles(child, result);
	// }
	// }

}
