package edu.udel.cis.vsl.civl;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.PrintStream;
import java.io.PrintWriter;
import java.util.ArrayList;

import edu.udel.cis.vsl.abc.ABC;
import edu.udel.cis.vsl.abc.ast.unit.IF.TranslationUnit;
import edu.udel.cis.vsl.abc.parse.IF.ParseException;
import edu.udel.cis.vsl.abc.preproc.Preprocess;
import edu.udel.cis.vsl.abc.preproc.IF.Preprocessor;
import edu.udel.cis.vsl.abc.preproc.IF.PreprocessorException;
import edu.udel.cis.vsl.abc.preproc.IF.PreprocessorFactory;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;
import edu.udel.cis.vsl.civl.kripke.Enabler;
import edu.udel.cis.vsl.civl.kripke.StateManager;
import edu.udel.cis.vsl.civl.library.CommonLibraryExecutorLoader;
import edu.udel.cis.vsl.civl.log.ErrorLog;
import edu.udel.cis.vsl.civl.model.Models;
import edu.udel.cis.vsl.civl.model.IF.Model;
import edu.udel.cis.vsl.civl.model.IF.ModelBuilder;
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

	private static SymbolicUniverse universe = SARL.newStandardUniverse();
	private static ModelBuilder modelBuilder = Models.newModelBuilder();

	// TODO:
	// add -D support. Need to create a token with "source" the command line.
	// may treat command line as (virtual) file called "commandline"?

	public static void main(String[] args) throws PreprocessorException,
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
		if (infileName == null)
			throw new IllegalArgumentException("No input file specified");
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
			check(infile, out);
		}
	}

	public static boolean check(File file, PrintStream out)
			throws SyntaxException, ParseException, PreprocessorException {
		TranslationUnit unit;
		StateFactoryIF stateFactory = new StateFactory(universe);
		Model model;
		TransitionFactory transitionFactory = new TransitionFactory();
		ErrorLog log = new ErrorLog(new PrintWriter(System.out),
				new java.io.File("."));
		Evaluator evaluator = new Evaluator(universe, log);
		EnablerIF<State, Transition, TransitionSequence> enabler = new Enabler(
				transitionFactory, universe, evaluator);
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

		try {
			unit = ABC.activator(file).getSideEffectFreeTranslationUnit();
		} catch (SyntaxException e) {
			System.out.println("Syntax error in " + file.getName() + ": \n"
					+ e.getMessage());
			return false;
		} catch (ParseException e) {
			System.out.println("Error parsing " + file.getName() + ": \n"
					+ e.getMessage());
			return false;
		} catch (PreprocessorException e) {
			System.out.println("Error preprocessing " + file.getName() + ": \n"
					+ e.getMessage());
			return false;
		}
		model = modelBuilder.buildModel(unit);
		out.println(bar + " Model " + bar + "\n");
		model.print(out);
		initialState = stateFactory.initialState(model);
		executor = new Executor(model, universe, stateFactory, log, loader);
		stateManager = new StateManager(executor);
		searcher = new DfsSearcher<State, Transition, TransitionSequence>(
				enabler, stateManager, predicate);
		searcher.setDebugOut(new PrintWriter(out));
		result = searcher.search(initialState);
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
		return result;
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
}
