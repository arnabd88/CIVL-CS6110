package edu.udel.cis.vsl.civl.run;

import java.io.File;
import java.io.PrintStream;
import java.util.Random;

import edu.udel.cis.vsl.civl.kripke.Enabler;
import edu.udel.cis.vsl.civl.kripke.StateManager;
import edu.udel.cis.vsl.civl.library.CommonLibraryExecutorLoader;
import edu.udel.cis.vsl.civl.model.IF.Model;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.predicate.StandardPredicate;
import edu.udel.cis.vsl.civl.semantics.Evaluator;
import edu.udel.cis.vsl.civl.semantics.Executor;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutorLoader;
import edu.udel.cis.vsl.civl.state.States;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.StateFactory;
import edu.udel.cis.vsl.civl.transition.Transition;
import edu.udel.cis.vsl.civl.transition.TransitionFactory;
import edu.udel.cis.vsl.civl.transition.TransitionSequence;
import edu.udel.cis.vsl.gmc.CommandLineException;
import edu.udel.cis.vsl.gmc.EnablerIF;
import edu.udel.cis.vsl.gmc.ErrorLog;
import edu.udel.cis.vsl.gmc.GMCConfiguration;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;

/**
 * Base class for various tools that require executing a CIVL model. It provides
 * some of the services needed by most such tools. A concrete tool can extend
 * this class, or delegate to an instance of it.
 * 
 * @author Stephen F. Siegel
 * 
 */
public abstract class Player {

	protected GMCConfiguration config;

	protected Model model;

	protected PrintStream out;

	protected String sessionName;

	protected ModelFactory modelFactory;

	protected StateFactory stateFactory;

	protected TransitionFactory transitionFactory;

	protected ErrorLog log;

	protected Evaluator evaluator;

	protected EnablerIF<State, Transition, TransitionSequence> enabler;

	protected StandardPredicate predicate;

	protected LibraryExecutorLoader loader;

	protected Executor executor;

	protected StateManager stateManager;

	protected boolean random;

	protected boolean verbose;

	protected boolean debug;

	protected boolean showStates;

	protected boolean showSavedStates;

	protected boolean showTransitions;

	protected String result;

	protected boolean minimize;

	protected int maxdepth;

	protected boolean scpPor; // false by default

	protected boolean saveStates; // true by default

	protected boolean simplify; // true by default

	protected boolean solve; // false by default

	protected boolean enablePrintf; // true by default

	public Player(GMCConfiguration config, Model model, PrintStream out)
			throws CommandLineException {
		SymbolicUniverse universe;
		String stateOption = (String) config
				.getValueOrDefault(UserInterface.statesO);

		this.config = config;
		this.model = model;
		this.out = out;
		this.sessionName = model.name();
		this.modelFactory = model.factory();
		universe = modelFactory.universe();
		if ("transient".equals(stateOption))
			this.stateFactory = States.newTransientStateFactory(modelFactory);
		else if ("immutable".equals(stateOption))
			this.stateFactory = States.newImmutableStateFactory(modelFactory);
		else if ("persistent".equals(stateOption))
			this.stateFactory = States.newPersistentStateFactory(modelFactory);
		else
			throw new CommandLineException("Unknown state implementation: "
					+ stateOption);
		this.transitionFactory = new TransitionFactory();
		this.log = new ErrorLog(new File("CIVLREP"), sessionName, out);
		this.evaluator = new Evaluator(config, modelFactory, stateFactory, log);
		evaluator.setSolve(solve);
		this.predicate = new StandardPredicate(log, universe, evaluator);
		this.loader = new CommonLibraryExecutorLoader();
		this.log.setErrorBound((int) config
				.getValueOrDefault(UserInterface.errorBoundO));
		this.enablePrintf = (Boolean) config
				.getValueOrDefault(UserInterface.enablePrintfO);
		this.executor = new Executor(config, modelFactory, stateFactory, log,
				loader, out, this.enablePrintf);
		this.random = config.isTrue(UserInterface.randomO);
		this.verbose = config.isTrue(UserInterface.verboseO);
		this.debug = config.isTrue(UserInterface.debugO);
		this.showStates = config.isTrue(UserInterface.showStatesO);
		this.showSavedStates = config.isTrue(UserInterface.showSavedStatesO);
		this.showTransitions = config.isTrue(UserInterface.showTransitionsO);
		this.minimize = config.isTrue(UserInterface.minO);
		this.maxdepth = (int) config.getValueOrDefault(UserInterface.maxdepthO);
		this.scpPor = ((String) config.getValueOrDefault(UserInterface.porO))
				.equalsIgnoreCase("scp");
		this.saveStates = (Boolean) config
				.getValueOrDefault(UserInterface.saveStatesO);
		this.simplify = (Boolean) config
				.getValueOrDefault(UserInterface.simplifyO);
		this.solve = (Boolean) config.getValueOrDefault(UserInterface.solveO);
		
		if (this.random) {
			long seed;
			String seedString = (String) config.getValue(UserInterface.seedO);

			if (seedString == null)
				seed = System.currentTimeMillis();
			else
				try {
					seed = new Long(seedString);
				} catch (NumberFormatException e) {
					throw new CommandLineException(
							"Expected long value for seed, saw: " + seedString);
				}
			out.println("Random execution with seed " + seed + ".");
			enabler = new Enabler(transitionFactory, evaluator, executor,
					random, new Random(seed), this.scpPor);
			enabler.setDebugOut(out);
		} else {
			enabler = new Enabler(transitionFactory, evaluator, executor,
					this.scpPor);
			enabler.setDebugOut(out);
			enabler.setDebugging(debug);
		}
		stateManager = new StateManager(executor);
		stateManager.setOutputStream(out);
		stateManager.setVerbose(verbose);
		stateManager.setDebug(debug);
		stateManager.setShowStates(showStates);
		stateManager.setShowSavedStates(showSavedStates);
		stateManager.setShowTransitions(showTransitions);
		stateManager.setSaveStates(saveStates);
		stateManager.setSimplify(simplify);
	}

	public void printResult() {
		out.println(result);
	}

}
