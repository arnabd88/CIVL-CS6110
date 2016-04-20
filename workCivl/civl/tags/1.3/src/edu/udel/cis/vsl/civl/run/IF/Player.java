package edu.udel.cis.vsl.civl.run.IF;

import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.errorBoundO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.guiO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.maxdepthO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.minO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.randomO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.solveO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.statsBar;

import java.io.File;
import java.io.PrintStream;

import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.config.IF.CIVLConstants.DeadlockKind;
import edu.udel.cis.vsl.civl.dynamic.IF.Dynamics;
import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.kripke.IF.Enabler;
import edu.udel.cis.vsl.civl.kripke.IF.Kripkes;
import edu.udel.cis.vsl.civl.kripke.IF.LibraryEnablerLoader;
import edu.udel.cis.vsl.civl.kripke.IF.StateManager;
import edu.udel.cis.vsl.civl.log.IF.CIVLErrorLogger;
import edu.udel.cis.vsl.civl.model.IF.Model;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.predicate.IF.AndPredicate;
import edu.udel.cis.vsl.civl.predicate.IF.CIVLStatePredicate;
import edu.udel.cis.vsl.civl.predicate.IF.Predicates;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluator;
import edu.udel.cis.vsl.civl.semantics.IF.Executor;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryEvaluatorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.Semantics;
import edu.udel.cis.vsl.civl.semantics.IF.SymbolicAnalyzer;
import edu.udel.cis.vsl.civl.semantics.IF.Transition;
import edu.udel.cis.vsl.civl.semantics.IF.TransitionSequence;
import edu.udel.cis.vsl.civl.state.IF.MemoryUnitFactory;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.StateFactory;
import edu.udel.cis.vsl.civl.state.IF.States;
import edu.udel.cis.vsl.gmc.CommandLineException;
import edu.udel.cis.vsl.gmc.EnablerIF;
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

	protected String sessionName;

	protected ModelFactory modelFactory;

	protected StateFactory stateFactory;

	protected MemoryUnitFactory memUnitFactory;

	protected Evaluator evaluator;

	protected EnablerIF<State, Transition, TransitionSequence> enabler;

	protected CIVLStatePredicate predicate = null;

	protected LibraryEnablerLoader libraryEnablerLoader;

	protected LibraryExecutorLoader libraryExecutorLoader;

	protected LibraryEvaluatorLoader libraryEvaluatorLoader;

	protected Executor executor;

	protected StateManager stateManager;

	protected boolean random;

	protected String result;

	protected boolean minimize;

	protected int maxdepth;

	protected boolean solve; // false by default

	protected boolean gui; // false by default, only works with Replay mode.

	protected SymbolicUtility symbolicUtil;

	protected SymbolicAnalyzer symbolicAnalyzer;

	protected CIVLErrorLogger log;

	protected CIVLConfiguration civlConfig;

	public Player(GMCConfiguration config, Model model, PrintStream out,
			PrintStream err, boolean collectOutputs)
			throws CommandLineException {
		SymbolicUniverse universe;

		this.config = config;
		this.model = model;
		civlConfig = new CIVLConfiguration(config.getAnonymousSection());
		civlConfig.setOut(out);
		civlConfig.setErr(err);
		civlConfig.setCollectOutputs(collectOutputs);
		this.sessionName = model.name();
		this.modelFactory = model.factory();
		universe = modelFactory.universe();
		this.solve = (Boolean) config.getAnonymousSection().getValueOrDefault(
				solveO);
		this.log = new CIVLErrorLogger(new File("CIVLREP"), sessionName, out,
				config, universe, solve);
		this.log.setErrorBound((int) config.getAnonymousSection()
				.getValueOrDefault(errorBoundO));
		this.symbolicUtil = Dynamics.newSymbolicUtility(universe, modelFactory);
		this.memUnitFactory = States.newImmutableMemoryUnitFactory(universe,
				modelFactory);
		this.stateFactory = States.newImmutableStateFactory(modelFactory,
				symbolicUtil, memUnitFactory, config);
		this.libraryEvaluatorLoader = Semantics
				.newLibraryEvaluatorLoader(this.civlConfig);
		this.symbolicAnalyzer = Semantics.newSymbolicAnalyzer(this.civlConfig,
				universe, modelFactory, symbolicUtil);
		this.evaluator = Semantics.newEvaluator(modelFactory, stateFactory,
				libraryEvaluatorLoader, symbolicUtil, symbolicAnalyzer,
				memUnitFactory, log);
		this.gui = (Boolean) config.getAnonymousSection().getValueOrDefault(
				guiO);
		this.libraryExecutorLoader = Semantics.newLibraryExecutorLoader(
				this.libraryEvaluatorLoader, this.civlConfig);
		this.executor = Semantics.newExecutor(modelFactory, stateFactory, log,
				libraryExecutorLoader, evaluator, symbolicAnalyzer, log,
				civlConfig);
		this.random = config.getAnonymousSection().isTrue(randomO);
		this.minimize = config.getAnonymousSection().isTrue(minO);
		this.maxdepth = (int) config.getAnonymousSection().getValueOrDefault(
				maxdepthO);
		this.libraryEnablerLoader = Kripkes.newLibraryEnablerLoader(
				this.libraryEvaluatorLoader, this.civlConfig);
		enabler = Kripkes.newEnabler(stateFactory, evaluator, symbolicAnalyzer,
				memUnitFactory, this.libraryEnablerLoader, log, civlConfig);
		if (civlConfig.deadlock() == DeadlockKind.ABSOLUTE) {
			this.addPredicate(Predicates.newDeadlock(universe,
					(Enabler) this.enabler, symbolicAnalyzer));
		} else if (civlConfig.deadlock() == DeadlockKind.POTENTIAL) {
			this.addPredicate(Predicates.newPotentialDeadlock(universe,
					(Enabler) this.enabler, libraryEnablerLoader, evaluator,
					modelFactory, symbolicUtil, symbolicAnalyzer));
		}
		// else {
		// this.predicates = null;
		// }
		stateManager = Kripkes.newStateManager((Enabler) enabler, executor,
				symbolicAnalyzer, log, civlConfig);
	}

	// protected CIVLExecutionException getCurrentViolation() {
	// CIVLExecutionException violation = null;
	//
	// for (CIVLStatePredicate predicate : this.predicates) {
	// violation = predicate.getUnreportedViolation();
	// if (violation != null)
	// break;
	// }
	// return violation;
	// }

	public void printResult() {
		civlConfig.out().println(statsBar + " Result " + statsBar);
		civlConfig.out().println(result);
	}

	public void addPredicate(CIVLStatePredicate newPredicate) {
		if (this.predicate == null)
			this.predicate = newPredicate;
		else {
			if (!this.predicate.isAndPredicate()) {
				this.predicate = Predicates.newAndPredicate(this.predicate);
			}
			((AndPredicate) this.predicate).addClause(newPredicate);
		}
	}

	public StateManager stateManager() {
		return this.stateManager;
	}
}
