package edu.udel.cis.vsl.civl.run;

import java.io.File;
import java.io.PrintStream;

import edu.udel.cis.vsl.civl.kripke.Enabler;
import edu.udel.cis.vsl.civl.kripke.PointeredEnabler;
import edu.udel.cis.vsl.civl.kripke.ScopedEnabler;
import edu.udel.cis.vsl.civl.kripke.StateManager;
import edu.udel.cis.vsl.civl.library.CommonLibraryLoader;
import edu.udel.cis.vsl.civl.library.IF.LibraryLoader;
import edu.udel.cis.vsl.civl.model.IF.Model;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.predicate.StandardPredicate;
import edu.udel.cis.vsl.civl.semantics.CommonEvaluator;
import edu.udel.cis.vsl.civl.semantics.CommonExecutor;
import edu.udel.cis.vsl.civl.semantics.MPIExecutor;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluator;
import edu.udel.cis.vsl.civl.semantics.IF.Executor;
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

	protected LibraryLoader libraryLoader;

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

	protected boolean showAmpleSet; // false by default

	protected boolean scpPor1; // false by default

	protected boolean scpPor2; // false by default

	protected boolean saveStates; // true by default

	protected boolean simplify; // true by default

	protected boolean solve; // false by default

	protected boolean enablePrintf; // true by default

	protected boolean mpiMode; // false by default
	
	protected boolean gui; // false by default, only works with Replay mode.

	public Player(GMCConfiguration config, Model model, PrintStream out)
			throws CommandLineException {
		SymbolicUniverse universe;

		this.config = config;
		this.model = model;
		this.out = out;
		this.sessionName = model.name();
		this.modelFactory = model.factory();
		universe = modelFactory.universe();
		this.stateFactory = States.newImmutableStateFactory(modelFactory,
				config);
		this.transitionFactory = new TransitionFactory();
		this.log = new ErrorLog(new File("CIVLREP"), sessionName, out);
		this.evaluator = new CommonEvaluator(config, modelFactory,
				stateFactory, log);
		evaluator.setSolve(solve);
		this.libraryLoader = new CommonLibraryLoader();
		this.log.setErrorBound((int) config
				.getValueOrDefault(UserInterface.errorBoundO));
		this.enablePrintf = (Boolean) config
				.getValueOrDefault(UserInterface.enablePrintfO);
		this.showAmpleSet = (Boolean) config
				.getValueOrDefault(UserInterface.showAmpleSetO);
		this.gui = (Boolean) config
				.getValueOrDefault(UserInterface.guiO);
		this.mpiMode = (Boolean) config.getValueOrDefault(UserInterface.mpiO);
		if (this.mpiMode)
			this.executor = new MPIExecutor(config, modelFactory, stateFactory,
					log, libraryLoader, out, this.enablePrintf, evaluator);
		else
			this.executor = new CommonExecutor(config, modelFactory,
					stateFactory, log, libraryLoader, out, this.enablePrintf,
					evaluator);
		// this.evaluator.setExecutor(executor);
		this.predicate = new StandardPredicate(log, universe, this.executor);
		this.random = config.isTrue(UserInterface.randomO);
		this.verbose = config.isTrue(UserInterface.verboseO);
		this.debug = config.isTrue(UserInterface.debugO);
		this.showStates = config.isTrue(UserInterface.showStatesO);
		this.showSavedStates = config.isTrue(UserInterface.showSavedStatesO);
		this.showTransitions = config.isTrue(UserInterface.showTransitionsO);
		this.minimize = config.isTrue(UserInterface.minO);
		this.maxdepth = (int) config.getValueOrDefault(UserInterface.maxdepthO);
		this.scpPor1 = ((String) config.getValueOrDefault(UserInterface.porO))
				.equalsIgnoreCase("scp1");
		this.scpPor2 = ((String) config.getValueOrDefault(UserInterface.porO))
				.equalsIgnoreCase("scp2");
		this.saveStates = (Boolean) config
				.getValueOrDefault(UserInterface.saveStatesO);
		this.simplify = (Boolean) config
				.getValueOrDefault(UserInterface.simplifyO);
		this.solve = (Boolean) config.getValueOrDefault(UserInterface.solveO);
		if (this.scpPor1) {
			enabler = new ScopedEnabler(transitionFactory, evaluator, executor,
					false, showAmpleSet, this.libraryLoader);
		} else if (this.scpPor2) {
			enabler = new ScopedEnabler(transitionFactory, evaluator, executor,
					true, showAmpleSet, this.libraryLoader);
		} else {
			enabler = new PointeredEnabler(transitionFactory, evaluator,
					executor, showAmpleSet, this.libraryLoader);
		}
		enabler.setDebugOut(out);
		enabler.setDebugging(debug);
		this.executor.setEnabler((Enabler) this.enabler);
		this.evaluator.setEnabler((Enabler) this.enabler);
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
