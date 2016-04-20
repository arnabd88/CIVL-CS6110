package edu.udel.cis.vsl.civl.kripke.common;

import java.io.PrintStream;
import java.util.LinkedList;
import java.util.List;

import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.kripke.IF.Enabler;
import edu.udel.cis.vsl.civl.kripke.IF.LibraryEnabler;
import edu.udel.cis.vsl.civl.kripke.IF.LibraryEnablerLoader;
import edu.udel.cis.vsl.civl.log.IF.CIVLErrorLogger;
import edu.udel.cis.vsl.civl.log.IF.CIVLExecutionException;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.Certainty;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.ErrorKind;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.SystemFunction;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.CallOrSpawnStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.model.IF.statement.StatementList;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluation;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluator;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryLoaderException;
import edu.udel.cis.vsl.civl.semantics.IF.Semantics;
import edu.udel.cis.vsl.civl.semantics.IF.SymbolicAnalyzer;
import edu.udel.cis.vsl.civl.semantics.IF.Transition;
import edu.udel.cis.vsl.civl.semantics.IF.TransitionSequence;
import edu.udel.cis.vsl.civl.state.IF.ProcessState;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.StateFactory;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.gmc.EnablerIF;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;

/**
 * CommonEnabler implements {@link EnablerIF} for CIVL models. It is an abstract
 * class and can have different implementations for different reduction
 * techniques.
 * 
 * @author Manchun Zheng (zmanchun)
 * @author Timothy K. Zirkel (zirkel)
 */
public abstract class CommonEnabler implements Enabler {

	/* *************************** Instance Fields ************************* */

	/**
	 * Turn on/off debugging option to print more information.
	 */
	protected boolean debugging = false;

	/**
	 * The output stream for printing debugging information.
	 */
	protected PrintStream debugOut = System.out;

	/**
	 * The unique evaluator used by the system.
	 */
	protected Evaluator evaluator;

	/**
	 * The unique model factory used by the system.
	 */
	protected ModelFactory modelFactory;

	/**
	 * The option to enable/disable the printing of ample sets of each state.
	 */
	protected boolean showAmpleSet = false;

	/**
	 * The unique symbolic universe used by the system.
	 */
	protected SymbolicUniverse universe;

	/**
	 * The symbolic expression for the boolean value false.
	 */
	protected BooleanExpression falseExpression;

	/**
	 * The library enabler loader.
	 */
	protected LibraryEnablerLoader libraryLoader;

	/**
	 * Show ample sets with the states?
	 */
	protected boolean showAmpleSetWtStates = false;

	/**
	 * The state factory that provides operations on states.
	 */
	protected StateFactory stateFactory;

	/**
	 * The error logger for reporting errors.
	 */
	protected CIVLErrorLogger errorLogger;

	/**
	 *  The symbolic analyzer to be used.
	 */
	protected SymbolicAnalyzer symbolicAnalyzer;

	/* ***************************** Constructor *************************** */

	/**
	 * Creates a new instance of Enabler, called by the constructors of the
	 * classes that implements Enabler.
	 * 
	 * @param transitionFactory
	 *            The transition factory to be used for composing new
	 *            transitions.
	 * @param evaluator
	 *            The evaluator to be used for evaluating expressions.
	 * @param executor
	 *            The executor to be used for computing the guard of system
	 *            functions.
	 * @param symbolicAnalyzer
	 *            The symbolic analyzer used in the system.
	 * @param showAmpleSet
	 *            The option to enable or disable the printing of ample sets.
	 */
	protected CommonEnabler(StateFactory stateFactory, Evaluator evaluator,
			SymbolicAnalyzer symbolicAnalyzer, LibraryEnablerLoader libLoader,
			CIVLErrorLogger errorLogger, CIVLConfiguration civlConfig) {
		this.errorLogger = errorLogger;
		this.evaluator = evaluator;
		this.symbolicAnalyzer = symbolicAnalyzer;
		this.debugOut = civlConfig.out();
		this.debugging = civlConfig.debug();
		this.showAmpleSet = civlConfig.showAmpleSet()
				|| civlConfig.showAmpleSetWtStates();
		this.showAmpleSetWtStates = civlConfig.showAmpleSetWtStates();
		this.modelFactory = evaluator.modelFactory();
		this.universe = modelFactory.universe();
		falseExpression = universe.falseExpression();
		this.libraryLoader = libLoader;
		this.stateFactory = stateFactory;
	}

	/* ************************ Methods from EnablerIF ********************* */

	@Override
	public TransitionSequence enabledTransitions(State state) {
		TransitionSequence transitions;

		if (state.getPathCondition().isFalse())
			// return empty set of transitions.
			return Semantics.newTransitionSequence(state);
		// return resumable atomic transitions.
		transitions = enabledAtomicTransitions(state);
		if (transitions == null)
			// return ample transitions.
			transitions = enabledTransitionsPOR(state);
		return transitions;
	}

	@Override
	public boolean debugging() {
		return debugging;
	}

	@Override
	public PrintStream getDebugOut() {
		return debugOut;
	}

	/* **************************** Public Methods ************************* */

	@Override
	public Evaluation getGuard(Statement statement, int pid, State state) {
		try {
			return evaluator.evaluate(state, pid, statement.guard());
		} catch (UnsatisfiablePathConditionException e) {
			return new Evaluation(state, this.falseExpression);
		}
	}

	@Override
	public boolean hasMultiple(TransitionSequence sequence) {
		return sequence.numRemoved() + sequence.size() > 1;
	}

	@Override
	public boolean hasNext(TransitionSequence transitionSequence) {
		return !transitionSequence.isEmpty();
	}

	@Override
	public Transition next(TransitionSequence transitionSequence) {
		return transitionSequence.remove();
	}

	@Override
	public int numRemoved(TransitionSequence sequence) {
		return sequence.numRemoved();
	}

	@Override
	public Transition peek(TransitionSequence transitionSequence) {
		return transitionSequence.peek();
	}

	@Override
	public void print(PrintStream out, TransitionSequence transitionSequence) {
	}

	@Override
	public void printFirstTransition(PrintStream arg0, TransitionSequence arg1) {
	}

	@Override
	public void printRemaining(PrintStream arg0, TransitionSequence arg1) {
	}

	@Override
	public void setDebugOut(PrintStream debugOut) {
		this.debugOut = debugOut;
	}

	@Override
	public void setDebugging(boolean debugging) {
		this.debugging = debugging;
	}

	@Override
	public State source(TransitionSequence transitionSequence) {
		return transitionSequence.state();
	}

	/* ************************ Package-private Methods ******************** */

	/**
	 * Obtain enabled transitions with partial order reduction. May have
	 * different implementation of POR algorithms.
	 * 
	 * @param state
	 *            The current state.
	 * @return The enabled transitions computed by a certain POR approach.
	 */
	abstract TransitionSequence enabledTransitionsPOR(State state);

	/**
	 * Get the enabled transitions of a certain process at a given state.
	 * 
	 * @param state
	 *            The state to work with.
	 * @param pid
	 *            The process id to work with.
	 * @param assignAtomicLock
	 *            The assignment statement for the atomic lock variable, should
	 *            be null except that the process is going to re-obtain the
	 *            atomic lock variable.
	 * @return the list of enabled transitions of the given process at the
	 *         specified state
	 */
	List<Transition> enabledTransitionsOfProcess(State state, int pid) {
		ProcessState p = state.getProcessState(pid);
		Location pLocation = p.getLocation();
		LinkedList<Transition> transitions = new LinkedList<>();
		Statement assignAtomicLock = null;
		int numOutgoing;

		if (pLocation == null)
			return transitions;
		if (stateFactory.processInAtomic(state) != pid && p.atomicCount() > 0) {
			assignAtomicLock = modelFactory.assignAtomicLockVariable(pid,
					pLocation);
		}
		numOutgoing = pLocation.getNumOutgoing();
		for (int i = 0; i < numOutgoing; i++) {
			Statement statement = pLocation.getOutgoing(i);
			BooleanExpression newPathCondition = newPathCondition(state, pid,
					statement);

			if (!newPathCondition.isFalse()) {
				transitions.addAll(enabledTransitionsOfStatement(state,
						statement, newPathCondition, pid, assignAtomicLock));
			}
		}
		return transitions;
	}

	LibraryEnabler libraryEnabler(CIVLSource civlSource, String library)
			throws LibraryLoaderException {
		return this.libraryLoader.getLibraryEnabler(library, this, evaluator,
				evaluator.modelFactory(), evaluator.symbolicUtility(),
				this.symbolicAnalyzer);
	}

	/* **************************** Private Methods ************************ */

	/**
	 * Computes transitions from the process owning the atomic lock or triggered
	 * by resuming an atomic block that is previously blocked. Add an assignment
	 * to update atomic lock variable (i.e., grabbing the atomic lock) and mean
	 * 
	 * @param state
	 *            The current state.
	 * @return The enabled transitions that resume an atomic block.
	 */
	private TransitionSequence enabledAtomicTransitions(State state) {
		int pidInAtomic;

		pidInAtomic = stateFactory.processInAtomic(state);
		if (pidInAtomic >= 0) {
			// execute a transition in an atomic block of a certain process
			// without interleaving with other processes
			TransitionSequence localTransitions = Semantics
					.newTransitionSequence(state);

			localTransitions.addAll(enabledTransitionsOfProcess(state,
					pidInAtomic));
			if (!localTransitions.isEmpty())
				return localTransitions;
		}
		return null;
	}

	/**
	 * Get the enabled transitions of a statement at a certain state. An
	 * assignment to the atomic lock variable might be forced to the returned
	 * transitions, when the process is going to re-obtain the atomic lock
	 * variable.
	 * 
	 * @param state
	 *            The state to work with.
	 * @param s
	 *            The statement to be used to generate transitions.
	 * @param pathCondition
	 *            The current path condition.
	 * @param pid
	 *            The process id that the statement belongs to.
	 * @param assignAtomicLock
	 *            The assignment statement for the atomic lock variable, should
	 *            be null except that the process is going to re-obtain the
	 *            atomic lock variable.
	 * @return The set of enabled transitions.
	 */
	private List<Transition> enabledTransitionsOfStatement(State state,
			Statement s, BooleanExpression pathCondition, int pid,
			Statement assignAtomicLock) {
		List<Transition> localTransitions = new LinkedList<>();
		Statement transitionStatement = null;
		int processIdentifier = state.getProcessState(pid).identifier();

		try {
			if (s instanceof CallOrSpawnStatement) {
				CallOrSpawnStatement call = (CallOrSpawnStatement) s;

				// TODO think about optimization of system functions
				if (call.isSystemCall()) // TODO check function pointer
					return this.getEnabledTransitionsOfSystemCall(
							call.getSource(), state, call, pathCondition, pid,
							processIdentifier, assignAtomicLock);
				else
					transitionStatement = s;
			} else
				transitionStatement = s;
			if (transitionStatement != null) {
				if (assignAtomicLock != null) {
					StatementList statementList = modelFactory
							.statmentList(assignAtomicLock);

					statementList.add(s);
					transitionStatement = statementList;
				} else
					transitionStatement = s;
				localTransitions.add(Semantics.newTransition(pathCondition,
						pid, processIdentifier, transitionStatement));
			}
		} catch (UnsatisfiablePathConditionException e) {
			// nothing to do: don't add this transition
		}
		return localTransitions;
	}

	/**
	 * Computes the set of enabled transitions of a system function call.
	 * 
	 * @param source
	 * @param state
	 * @param call
	 * @param pathCondition
	 * @param pid
	 * @param processIdentifier
	 * @param assignAtomicLock
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private List<Transition> getEnabledTransitionsOfSystemCall(
			CIVLSource source, State state, CallOrSpawnStatement call,
			BooleanExpression pathCondition, int pid, int processIdentifier,
			Statement assignAtomicLock)
			throws UnsatisfiablePathConditionException {
		String libraryName = ((SystemFunction) call.function()).getLibrary();

		try {
			LibraryEnabler libEnabler = libraryEnabler(source, libraryName);

			return libEnabler.enabledTransitions(state, call, pathCondition,
					pid, processIdentifier, assignAtomicLock);
		} catch (LibraryLoaderException exception) {
			String process = state.getProcessState(pid).name() + "(id=" + pid
					+ ")";
			CIVLExecutionException err = new CIVLExecutionException(
					ErrorKind.LIBRARY, Certainty.PROVEABLE, process,
					"An error is encountered when loading the library enabler for "
							+ libraryName + ": " + exception.getMessage(),
					symbolicAnalyzer.stateToString(state), source);

			this.errorLogger.reportError(err);
		}
		return new LinkedList<Transition>();
	}

	/**
	 * Given a state, a process, and a statement, check if the statement's guard
	 * is satisfiable under the path condition. If it is, return the conjunction
	 * of the path condition and the guard. This will be the new path condition.
	 * Otherwise, return false.
	 * 
	 * @param state
	 *            The current state.
	 * @param pid
	 *            The id of the currently executing process.
	 * @param statement
	 *            The statement.
	 * @return The new path condition. False if the guard is not satisfiable
	 *         under the path condition.
	 */
	private BooleanExpression newPathCondition(State state, int pid,
			Statement statement) {
		Evaluation eval = getGuard(statement, pid, state);
		BooleanExpression guard = (BooleanExpression) eval.value;
		BooleanExpression pathCondition = eval.state.getPathCondition();
		Reasoner reasoner = universe.reasoner(pathCondition);

		if (guard.isTrue()) {
			return pathCondition;
		}
		if (reasoner.isValid(universe.not(guard)))
			return this.falseExpression;
		if (reasoner.isValid(guard))
			return pathCondition;
		return universe.and(pathCondition, guard);
	}
}
