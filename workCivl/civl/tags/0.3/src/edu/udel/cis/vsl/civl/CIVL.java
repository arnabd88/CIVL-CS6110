package edu.udel.cis.vsl.civl;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.PrintStream;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Random;

import edu.udel.cis.vsl.abc.ABC;
import edu.udel.cis.vsl.abc.parse.IF.ParseException;
import edu.udel.cis.vsl.abc.preproc.Preprocess;
import edu.udel.cis.vsl.abc.preproc.IF.Preprocessor;
import edu.udel.cis.vsl.abc.preproc.IF.PreprocessorException;
import edu.udel.cis.vsl.abc.preproc.IF.PreprocessorFactory;
import edu.udel.cis.vsl.abc.program.IF.Program;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;
import edu.udel.cis.vsl.civl.err.CIVLException;
import edu.udel.cis.vsl.civl.err.CIVLUnimplementedFeatureException;
import edu.udel.cis.vsl.civl.kripke.Enabler;
import edu.udel.cis.vsl.civl.kripke.StateManager;
import edu.udel.cis.vsl.civl.library.CommonLibraryExecutorLoader;
import edu.udel.cis.vsl.civl.log.ErrorLog;
import edu.udel.cis.vsl.civl.model.Models;
import edu.udel.cis.vsl.civl.model.IF.Model;
import edu.udel.cis.vsl.civl.model.IF.ModelBuilder;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.common.ABC_CIVLSource;
import edu.udel.cis.vsl.civl.predicate.StandardPredicate;
import edu.udel.cis.vsl.civl.semantics.Evaluator;
import edu.udel.cis.vsl.civl.semantics.Executor;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutorLoader;
import edu.udel.cis.vsl.civl.state.State;
import edu.udel.cis.vsl.civl.state.StateFactory;
import edu.udel.cis.vsl.civl.state.StateFactoryIF;
import edu.udel.cis.vsl.civl.transition.Transition;
import edu.udel.cis.vsl.civl.transition.TransitionFactory;
import edu.udel.cis.vsl.civl.transition.TransitionSequence;
import edu.udel.cis.vsl.gmc.DfsSearcher;
import edu.udel.cis.vsl.gmc.EnablerIF;
import edu.udel.cis.vsl.gmc.StateManagerIF;
import edu.udel.cis.vsl.gmc.StatePredicateIF;
import edu.udel.cis.vsl.sarl.SARL;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;

public class CIVL {

	public final static String version = "0.3";

	/** YYYY-MM-DD in accordance with ISO 8601 */
	public final static String date = "2013-11-20";

	// TODO:
	// add -D support. Need to create a token with "source" the command line.
	// may treat command line as (virtual) file called "commandline"?

	public static void main(String[] args) {
		try {
			mainWork(args);
		} catch (PreprocessorException e) {
			System.err.println("Preprocessing error: " + e.getMessage());
			System.exit(1);
		} catch (ParseException e) {
			System.err.println("Parse error: " + e.getMessage());
			System.exit(2);
		} catch (SyntaxException e) {
			System.err.println("Syntax error: " + e.getMessage());
			System.exit(3);
		} catch (FileNotFoundException e) {
			System.err.println("File not found: " + e.getMessage());
			System.exit(4);
		} catch (CIVLUnimplementedFeatureException e) {
			System.err.println(e.getMessage());
			System.exit(5);
		}
	}

	private static void mainWork(String[] args) throws PreprocessorException,
			ParseException, SyntaxException, FileNotFoundException {
		String infileName = null;
		String outfileName = null;
		// the following are updated by -I
		ArrayList<File> systemIncludeList = new ArrayList<File>();
		// the following are updated by -iquote
		ArrayList<File> userIncludeList = new ArrayList<File>();
		PreprocessorFactory preprocessorFactory;
		Preprocessor preprocessor;
		File infile;
		PrintStream out;
		File[] systemIncludes, userIncludes;
		boolean preprocOnly = false;
		boolean printModel = false;
		boolean verbose = false;
		boolean randomMode = false;

		System.out.println("CIVL v" + version + " of " + date
				+ " -- http://vsl.cis.udel.edu\n");
		System.out.flush();
		for (int i = 0; i < args.length; i++) {
			String arg = args[i];

			if (arg.startsWith("-o")) {
				String name;

				if (arg.length() == 2) {
					i++;
					if (i >= args.length)
						throw new IllegalArgumentException(
								"Filename must follow -o");
					name = args[i];
				} else {
					name = arg.substring(2);
				}
				if (outfileName == null)
					outfileName = name;
				else
					throw new IllegalArgumentException(
							"More than one use of -o");
			} else if (arg.startsWith("-I")) {
				String name;

				if (arg.length() == 2) {
					i++;
					if (i >= args.length)
						throw new IllegalArgumentException(
								"Filename must follow -I");
					name = args[i];
				} else {
					name = arg.substring(2);
				}
				systemIncludeList.add(new File(name));
			} else if (arg.startsWith("-iquote")) {
				String name;

				if (arg.length() == "-iquote".length()) {
					i++;
					if (i >= args.length)
						throw new IllegalArgumentException(
								"Filename must follow -iquote");
					name = args[i];
				} else {
					name = arg.substring("-iquote".length());
				}
				userIncludeList.add(new File(name));
			} else if (arg.equals("-E")) {
				preprocOnly = true;
			} else if (arg.equals("-P")) {
				printModel = true;
			} else if (arg.equals("-R")) {
				randomMode = true;
			} else if (arg.equals("-h") || arg.equals("-help")) {
				printUsage(new PrintStream(System.out));
				return;
			} else if (arg.equals("-v")) {
				verbose = true;
				printModel = true;
			} else if (arg.startsWith("-")) {
				throw new IllegalArgumentException(
						"Unknown command line option: " + arg);
			} else {
				if (infileName == null)
					infileName = arg;
				else
					throw new IllegalArgumentException(
							"More than one input file specified (previous was "
									+ infileName + "): " + arg);
			}
		}
		if (infileName == null) {
			printUsage(new PrintStream(System.out));
			return;
		}
		infile = new File(infileName);
		userIncludes = userIncludeList.toArray(new File[0]);
		systemIncludes = systemIncludeList.toArray(new File[0]);
		if (outfileName == null)
			out = System.out;
		else
			out = new PrintStream(new File(outfileName));
		preprocessorFactory = Preprocess.newPreprocessorFactory();
		preprocessor = preprocessorFactory.newPreprocessor(systemIncludes,
				userIncludes);
		if (preprocOnly) {
			preprocessor.printOutput(out, infile);
		} else {
			verify(printModel, verbose, infile, out, randomMode);
		}
		out.flush();
		if (outfileName != null) {
			out.close();
		}
	}

	public static boolean verify(File file, PrintStream out)
			throws SyntaxException, ParseException, PreprocessorException {
		return verify(false, false, file, out, false);
	}

	public static boolean verify(boolean printModel, boolean verbose,
			File file, PrintStream out) {
		return verify(printModel, verbose, file, out, false);
	}

	public static boolean verify(boolean printModel, boolean verbose,
			File file, PrintStream out, boolean randomMode) {
		SymbolicUniverse universe = SARL.newStandardUniverse();
		ModelBuilder modelBuilder = Models.newModelBuilder(universe);
		ModelFactory modelFactory = modelBuilder.factory();
		Program program;
		StateFactoryIF stateFactory = new StateFactory(modelFactory);
		Model model;
		TransitionFactory transitionFactory = new TransitionFactory();
		ErrorLog log = new ErrorLog(new PrintWriter(System.out), new File(
				new File("."), "CIVLREP/"));
		Evaluator evaluator = new Evaluator(modelFactory, stateFactory, log);
		EnablerIF<State, Transition, TransitionSequence> enabler;
		StatePredicateIF<State> predicate = new StandardPredicate(log,
				universe, evaluator);
		LibraryExecutorLoader loader = new CommonLibraryExecutorLoader();
		Executor executor;
		StateManagerIF<State, Transition> stateManager;
		DfsSearcher<State, Transition, TransitionSequence> searcher;
		State initialState;
		double startTime = System.currentTimeMillis(), endTime;
		boolean result;
		String bar = "===================";
		long seed = System.currentTimeMillis();

		log.setErrorBound(5);
		try {
			program = ABC.activator(file).getProgram();
			program.prune();
			program.removeSideEffects();
		} catch (SyntaxException e) {
			e.printStackTrace(System.err);
			System.err.flush();
			throw new CIVLException("Syntax error in " + file.getName()
					+ ": \n" + e.getMessage(),
					new ABC_CIVLSource(e.getSource()));
		} catch (ParseException e) {
			throw new CIVLException("Error parsing " + file.getName() + ": \n"
					+ e.getMessage(), null);
		} catch (PreprocessorException e) {
			throw new CIVLException("Error preprocessing " + file.getName()
					+ ": \n" + e.getMessage(), null);
		}
		model = modelBuilder.buildModel(program);
		if (printModel) {
			out.println(bar + " Model " + bar + "\n");
			model.print(out);
		}
		initialState = stateFactory.initialState(model);
		executor = new Executor(modelFactory, stateFactory, log, loader);
		if (randomMode) {
			System.out.println("Random execution with seed " + seed + ".");
			enabler = new Enabler(transitionFactory, evaluator, executor,
					randomMode, new Random(seed));
		} else {
			enabler = new Enabler(transitionFactory, evaluator, executor);
		}
		stateManager = new StateManager(executor);
		if (verbose) {
			((StateManager) stateManager).setDebugOut(out);
		}
		searcher = new DfsSearcher<State, Transition, TransitionSequence>(
				enabler, stateManager, predicate);
		searcher.setDebugOut(out);
		log.setSearcher(searcher);
		try {
			result = searcher.search(initialState);
		} catch (CIVLException e) {
			result = true;
			out.println(e);
			e.printStackTrace(out);
			out.println();
		}
		endTime = System.currentTimeMillis();
		out.println(bar + " Stats " + bar + "\n");
		CIVL.printStats(out, searcher, universe, startTime, endTime,
				((StateManager) stateManager).maxProcs());
		if (result || log.numReports() > 0) {
			out.println("The program MAY NOT be correct.");
		} else {
			out.println("The specified properties hold for all executions.");
		}
		out.flush();
		// Result is true if there is an error, but we want to return true if
		// there are no errors.
		return (!result) && (log.numReports() == 0);
	}

	public static void printStats(PrintStream out,
			DfsSearcher<State, Transition, TransitionSequence> searcher,
			SymbolicUniverse universe, double startTime, double endTime,
			int maxProcs) {
		long numStatesMatched = searcher.numStatesMatched();
		long numStatesSeen = searcher.numStatesSeen();
		long transitionsExecuted = searcher.numTransitions();
		long numProverValidCalls = universe.numValidCalls();
		long numCVC3Calls = universe.numProverValidCalls();
		long heapSize = Runtime.getRuntime().totalMemory();

		out.print("   maxProcs            : ");
		out.println(maxProcs);
		out.print("   statesSeen          : ");
		out.println(numStatesSeen);
		out.print("   statesMatched       : ");
		out.println(numStatesMatched);
		out.print("   transitionsExecuted : ");
		out.println(transitionsExecuted);
		out.print("   proverValidCalls    : ");
		out.println(numProverValidCalls);
		out.print("   CVC3ValidCalls      : ");
		out.println(numCVC3Calls);
		out.print("   memory (bytes)      : ");
		out.println(heapSize);
		out.print("   elapsedTime (s)     : ");
		out.println((endTime - startTime) / 1000.0);
	}

	public static void printUsage(PrintStream out) {
		out.println("Usage:");
		out.println("  civl [-help|-h]");
		out.println("  civl [options] model.cvl");
		out.println();
		out.println("Options:");
		out.println("-oOUTPUT_FILE");
		out.println("    direct output to file OUTPUT_FILE");
		out.println("-iINCLUDE_FILE");
		out.println("    add INCLUDE_FILE to the set of system includes");
		out.println("-iquoteINCLUDE_FILE");
		out.println("    add INCLUDE_FILE to the set of user includes");
		out.println("-P");
		out.println("    print the model");
		out.println("-v");
		out.println("    print the model and every state");
		out.println("-E");
		out.println("    stop after preprocessing the file and output the result");
		out.println("-R");
		out.println("    instead of full verification, execute a random path through the program");
		out.flush();
	}
}
