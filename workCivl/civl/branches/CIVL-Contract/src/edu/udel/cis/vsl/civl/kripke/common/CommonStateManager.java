/**
 * 
 */
package edu.udel.cis.vsl.civl.kripke.common;

import java.io.PrintStream;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.kripke.IF.Enabler;
import edu.udel.cis.vsl.civl.kripke.IF.StateManager;
import edu.udel.cis.vsl.civl.kripke.IF.TraceStep;
import edu.udel.cis.vsl.civl.kripke.common.StateStatus.EnabledStatus;
import edu.udel.cis.vsl.civl.log.IF.CIVLErrorLogger;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.ErrorKind;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.location.Location.AtomicKind;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.semantics.IF.Executor;
import edu.udel.cis.vsl.civl.semantics.IF.NoopTransition;
import edu.udel.cis.vsl.civl.semantics.IF.SymbolicAnalyzer;
import edu.udel.cis.vsl.civl.semantics.IF.Transition;
import edu.udel.cis.vsl.civl.semantics.IF.Transition.TransitionKind;
import edu.udel.cis.vsl.civl.semantics.IF.TransitionSequence;
import edu.udel.cis.vsl.civl.state.IF.CIVLHeapException;
import edu.udel.cis.vsl.civl.state.IF.CIVLHeapException.HeapErrorKind;
import edu.udel.cis.vsl.civl.state.IF.ProcessState;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.StateFactory;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.civl.util.IF.Pair;
import edu.udel.cis.vsl.civl.util.IF.Printable;
import edu.udel.cis.vsl.civl.util.IF.Utils;
import edu.udel.cis.vsl.gmc.TraceStepIF;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;

/**
 * @author Timothy K. Zirkel (zirkel)
 * @author Manchun Zheng (zmanchun)
 * @author Stephen F. Siegel (siegel)
 * 
 */
public class CommonStateManager implements StateManager {

	/* *************************** Instance Fields ************************* */

	/**
	 * The unique enabler instance used by the system
	 */
	private CommonEnabler enabler;

	/**
	 * The unique executor instance used by the system
	 */
	private Executor executor;

	private CIVLConfiguration config;

	/**
	 * The maximal number of processes at a state, initialized as 0.
	 */
	private int maxProcs = 0;

	/**
	 * The unique state factory used by the system.
	 */
	private StateFactory stateFactory;

	/**
	 * The object whose toString() method will be used to print the periodic
	 * update. The toString method of this object should print a short
	 * (one-line) message on the state of the search.
	 */
	private Printable updater;

	/**
	 * If true, print a short one-line update message on the state of the search
	 * at the next opportunity, and then set this flag back to false. This flag
	 * is typically set by a separate thread. Access to this thread is protected
	 * by the lock on this StateManager.
	 */

	/**
	 * Keep track of the maximal canonic ID of states. Since
	 * {@link StateFactory#canonic(State)} is only called when savedState option
	 * is enabled, this is only updated when savedState option is enabled. The
	 * motivation to have this field is to allow the state manager to print only
	 * new states in -savedStates mode, for better user experiences.
	 */
	private int maxCanonicId = -1;

	private CIVLErrorLogger errorLogger;

	/**
	 * The symbolic analyzer to be used.
	 */
	private SymbolicAnalyzer symbolicAnalyzer;

	private BooleanExpression falseExpr;

	private int numStatesExplored = 1;

	private OutputCollector outputCollector;

	private Stack<TransitionSequence> stack;

	private Set<Integer> expandedStateIDs = new HashSet<>();

	private boolean printTransitions;

	private boolean printAllStates;

	private boolean printSavedStates;

	// TODO: trying to fix this:
	// private boolean saveStates;

	/* ***************************** Constructor *************************** */

	/**
	 * Creates a new instance of state manager.
	 * 
	 * @param enabler
	 *            The enabler to be used.
	 * @param executor
	 *            The unique executor to by used in the system.
	 * @param symbolicAnalyzer
	 *            The symbolic analyzer to be used.
	 * @param errorLogger
	 *            The error logger to be used.
	 * @param config
	 *            The configuration of the civl model.
	 */
	public CommonStateManager(Enabler enabler, Executor executor,
			SymbolicAnalyzer symbolicAnalyzer, CIVLErrorLogger errorLogger,
			CIVLConfiguration config) {
		this.executor = executor;
		this.enabler = (CommonEnabler) enabler;
		this.stateFactory = executor.stateFactory();
		this.config = config;
		printTransitions = this.config.printTransitions()
				|| config.debugOrVerbose();
		printAllStates = this.config.debugOrVerbose()
				|| this.config.showStates();
		printSavedStates = printAllStates || this.config.showSavedStates();
		this.errorLogger = errorLogger;
		this.symbolicAnalyzer = symbolicAnalyzer;
		this.falseExpr = symbolicAnalyzer.getUniverse().falseExpression();
		if (config.collectOutputs())
			this.outputCollector = new OutputCollector(
					this.enabler.modelFactory.model());
	}

	/* *************************** Private Methods ************************* */
	/**
	 * Execute a transition (obtained by the enabler) of a state. When the
	 * corresponding process is in atomic/atom execution, continue to execute
	 * more statements as many as possible. Also execute more statements if
	 * possible.
	 * 
	 * @param state
	 *            The current state
	 * @param transition
	 *            The transition to be executed.
	 * @return the resulting trace step after executing the state.
	 * @throws UnsatisfiablePathConditionException
	 */
	private TraceStepIF<Transition, State> nextStateWork(State state,
			Transition transition) throws UnsatisfiablePathConditionException {
		int pid;
		int numProcs;
		int oldMaxCanonicId = this.maxCanonicId;
		int processIdentifier;
		Transition firstTransition;
		State oldState = state;
		StateStatus stateStatus;
		TraceStep traceStep;
		String process;
		int atomCount = 0;
		boolean ampleSetUpdated = false;
		int startStateId = state.getCanonicId();
		int sequenceId = 1;

		assert transition instanceof Transition;
		pid = ((Transition) transition).pid();
		processIdentifier = ((Transition) transition).processIdentifier();
		process = "p" + processIdentifier + " (id = " + pid + ")";
		traceStep = new CommonTraceStep(processIdentifier);
		firstTransition = (Transition) transition;
		if (state.getProcessState(pid).getLocation().enterAtom())
			atomCount = 1;
		// if (config.debug()) {
		// config.out().println(
		// "===========memory analysis at " + state + "=============");
		// stateFactory.printReachableMemoryUnits(config.out(), state);
		// }
		state = executor.execute(state, pid, firstTransition);
		if (printTransitions) {
			if (this.printSavedStates)
				config.out().println();
			printTransitionPrefix(oldState, processIdentifier);
			printStatement(oldState, state, firstTransition, AtomicKind.NONE,
					processIdentifier, false);
			oldState = state;
		}
		traceStep.addAtomicStep(new CommonAtomicStep(state, firstTransition));
		for (stateStatus = singleEnabled(state, pid, atomCount, process); stateStatus.val; stateStatus = singleEnabled(
				state, pid, stateStatus.atomCount, process)) {
			assert stateStatus.enabledTransition != null;
			assert stateStatus.enabledStatus == EnabledStatus.DETERMINISTIC;
			assert stateStatus.atomCount >= 0;
			if (this.printAllStates) {
				config.out().println();
				config.out().print(
						this.symbolicAnalyzer.stateToString(state,
								startStateId, sequenceId++));
			}
			state = executor.execute(state, pid, stateStatus.enabledTransition);
			numStatesExplored++;
			if (printTransitions) {
				if (this.printAllStates)
					config.out().println();
				printStatement(oldState, state, stateStatus.enabledTransition,
						AtomicKind.NONE, processIdentifier, false);
			}
			traceStep.addAtomicStep(new CommonAtomicStep(state,
					stateStatus.enabledTransition));
			oldState = state;
			// if (config.debug()) {
			// config.out().println(
			// "===========memory analysis at " + state
			// + "=============");
			// stateFactory.printReachableMemoryUnits(config.out(), state);
			// }
		}
		assert stateStatus.atomCount == 0;
		assert stateStatus.enabledStatus != EnabledStatus.DETERMINISTIC;
		if (stateStatus.enabledStatus == EnabledStatus.BLOCKED
				&& stateFactory.lockedByAtomic(state))
			state = stateFactory.releaseAtomicLock(state);
		if (printTransitions) {
			config.out().print("--> ");
		}
		if (config.saveStates()) {
			int newCanonicId;
			Set<HeapErrorKind> ignoredErrorSet = new HashSet<>();
			boolean finished = false;

			do {
				try {
					if (ignoredErrorSet.size() == 2)
						finished = true;
					state = stateFactory.canonic(state,
							config.collectProcesses(), config.collectScopes(),
							config.collectHeaps(), ignoredErrorSet);
					finished = true;
				} catch (CIVLHeapException hex) {
					// TODO state never gets canonicalized and then gmc can't
					// figure
					// out if it has been seen before.
					String message = "";

					state = hex.state();
					switch (hex.heapErrorKind()) {
					case NONEMPTY:
						message = "The dyscope " + hex.dyscopeName() + "(id="
								+ hex.dyscopeID()
								+ ") has a non-empty heap upon termination.\n";
						break;
					case UNREACHABLE:
						message = "An unreachable object (mallocID="
								+ hex.heapFieldID() + ", objectID="
								+ hex.heapObjectID()
								+ ") is detectd in the heap of dyscope "
								+ hex.dyscopeName() + "(id=" + hex.dyscopeID()
								+ ").\n";
						break;
					default:
					}
					message = message
							+ "heap"
							+ symbolicAnalyzer.symbolicExpressionToString(
									hex.source(), hex.state(), null,
									hex.heapValue());
					errorLogger.logSimpleError(hex.source(), state, process,
							symbolicAnalyzer.stateInformation(hex.state()),
							hex.kind(), message);
					ignoredErrorSet.add(hex.heapErrorKind());
				}
			} while (!finished);
			if (state.onStack()) {
				// this is a back-edge, we need to fulfill ample set condition
				// C3 cycle)
				TransitionSequence transitionSequence = stack.peek();
				State sourceState = transitionSequence.state();

				// if (expandedStateIDs.contains(sourceState.getCanonicId())
				// || expandedStateIDs.contains(state.getCanonicId()))
				// System.out.println("State " + state.getCanonicId()
				// + " is on stack but has been expanded before.");
				if (!expandedStateIDs.contains(sourceState.getCanonicId())
						&& !expandedStateIDs.contains(state.getCanonicId())
						&& !transitionSequence.containsAllEnabled()) {
					// int onStackID = state.getCanonicId();
					// Stack<TransitionSequence> tmp = new Stack<>();
					// TransitionSequence current = stack.pop();
					// State currentState = current.state();
					//
					// while (currentState.getCanonicId() != onStackID) {
					// tmp.push(current);
					// expandedStateIDs.add(currentState.getCanonicId());
					// current = stack.pop();
					// currentState = current.state();
					// }
					// expandedStateIDs.add(currentState.getCanonicId());
					// stack.push(current);
					// while (!tmp.isEmpty()) {
					// current = tmp.pop();
					// stack.push(current);
					// }
					expandedStateIDs.add(state.getCanonicId());
					expandedStateIDs.add(sourceState.getCanonicId());
					this.expandTransitionSequence(transitionSequence);
					ampleSetUpdated = true;
				}
			}
			traceStep.complete(state);
			newCanonicId = state.getCanonicId();
			if (newCanonicId > this.maxCanonicId) {
				this.maxCanonicId = newCanonicId;
				numStatesExplored++;
			}
		} else {
			// FIXME needs to commit all symbolic expressions?
			// if (config.collectProcesses())
			// state = stateFactory.collectProcesses(state);
			// try {
			// if (config.collectHeaps())
			// state = stateFactory.collectHeaps(state);
			// if (config.collectScopes())
			// state = stateFactory.collectScopes(state);
			// } catch (CIVLStateException stex) {
			// CIVLExecutionException err = new CIVLExecutionException(
			// stex.kind(), stex.certainty(), process, stex.message(),
			// symbolicAnalyzer.stateToString(stex.state()),
			// stex.source());
			//
			// errorLogger.reportError(err);
			// }
			if (config.simplify())
				state = stateFactory.simplify(state);
			traceStep.complete(state);
		}
		if (config.printTransitions())
			config.out().println(state);
		if (ampleSetUpdated
				&& (config.showAmpleSet() || config.showAmpleSetWtStates())) {
			State updatedState = stack.peek().state();

			config.out().println(
					"ample set at state " + updatedState.getCanonicId()
							+ " fully expanded");
		}
		if (printSavedStates
				&& (!config.saveStates() || this.maxCanonicId > oldMaxCanonicId)) {
			// in -savedStates mode, only print new states.
			config.out().println();
			config.out().print(this.symbolicAnalyzer.stateToString(state));
		} else if (config.showPathConditon()) {
			config.out().print(state.toString());
			config.out().print(" -- path condition: ");
			config.out().println(state.getPathCondition());
		}
		numProcs = state.numLiveProcs();
		if (numProcs > maxProcs)
			maxProcs = numProcs;
		if (config.collectOutputs())
			this.outputCollector.collectOutputs(state);
		return traceStep;
	}

	void expandTransitionSequence(TransitionSequence transitionSequence) {
		if (!transitionSequence.containsAllEnabled()) {
			State state = transitionSequence.state();
			TransitionSequence ampleSet = enabler.enabledTransitionsPOR(state);
			TransitionSequence enabledSet = enabler
					.enabledTransitionsOfAllProcesses(state);
			@SuppressWarnings("unchecked")
			Collection<Transition> difference = (Collection<Transition>) Utils
					.difference(enabledSet.transitions(),
							ampleSet.transitions());

			transitionSequence.setContainingAllEnabled(true);
			transitionSequence.addAll(difference);
		}
	}

	/**
	 * Analyzes if the current process has a single (deterministic) enabled
	 * transition at the given state. The point of this is that a sequence of
	 * these kind of transitions can be launched together to form a big
	 * transition. TODO Predicates are not checked for intermediate states.
	 * Conditions for a process p at a state s to execute more:
	 * <ul>
	 * <li>p is about to enter an atom block or p is already in some atom
	 * blocks:
	 * <ul>
	 * <li>the size of enabled(p, s) should be exactly 1;</li>
	 * <li>otherwise, an error will be reported.</li>
	 * </ul>
	 * </li> or
	 * <li>p is currently holding the atomic lock:
	 * <ol>
	 * <li>the current location of p has exactly one incoming statement;</li>
	 * <li>the size of enabled(p, s) should be exactly 1.</li>
	 * </ol>
	 * </li> or
	 * <li>the current location of p is purely local;
	 * <ul>
	 * <li>the size of enabled(p, s) is exactly 1.</li>
	 * </ul>
	 * </li>
	 * </ul>
	 * 
	 * @param state
	 *            The current state.
	 * @param pid
	 *            The ID of the current process.
	 * @param atomCount
	 *            The number of incomplete atom blocks.
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private StateStatus singleEnabled(State state, int pid, int atomCount,
			String process) throws UnsatisfiablePathConditionException {
		List<Transition> enabled;
		ProcessState procState = state.getProcessState(pid);
		Location pLocation;
		boolean inAtomic = false;
		boolean inAtom = false;

		if (procState == null || procState.hasEmptyStack())
			return new StateStatus(false, null, atomCount,
					EnabledStatus.TERMINATED);
		else
			pLocation = procState.getLocation();
		assert pLocation != null;
		enabled = enabler.enabledTransitionsOfProcess(state, pid);
		if (pLocation.enterAtom()) {
			if (atomCount == 0 && !pLocation.isPurelyLocal())
				return new StateStatus(false, null, 0, EnabledStatus.UNSAFE);
			atomCount++;
		} else if (pLocation.leaveAtom()) {
			inAtom = true;
			atomCount--;
		}
		if (inAtom || atomCount > 0) {
			// in atom execution
			if (enabled.size() == 1)
				return new StateStatus(true, enabled.get(0), atomCount,
						EnabledStatus.DETERMINISTIC);
			else if (enabled.size() > 1) {// non deterministic
				reportErrorForAtom(EnabledStatus.NONDETERMINISTIC, state,
						pLocation, process);
				return new StateStatus(false, null, atomCount,
						EnabledStatus.NONDETERMINISTIC);
			} else {// blocked
				reportErrorForAtom(EnabledStatus.BLOCKED, state, pLocation,
						process);
				return new StateStatus(false, null, atomCount,
						EnabledStatus.BLOCKED);
			}
		} else {
			int pidInAtomic = stateFactory.processInAtomic(state);

			if (pidInAtomic == pid) {
				// the process is in atomic execution
				// assert pidInAtomic == pid;
				if ((pLocation.getNumIncoming() > 1 && !pLocation.isSafeLoop())
						|| (pLocation.isStart() && pLocation.getNumIncoming() > 0))
					// possible loop, save state
					return new StateStatus(false, null, atomCount,
							EnabledStatus.LOOP_POSSIBLE);
				inAtomic = true;
			}
			if (inAtomic || pLocation.isPurelyLocal()) {
				if (enabled.size() == 1)
					return new StateStatus(true, enabled.get(0), atomCount,
							EnabledStatus.DETERMINISTIC);
				else if (enabled.size() > 1) // blocking
					return new StateStatus(false, null, atomCount,
							EnabledStatus.NONDETERMINISTIC);
				else
					return new StateStatus(false, null, atomCount,
							EnabledStatus.BLOCKED);
			}
			return new StateStatus(false, null, atomCount, EnabledStatus.NONE);
		}
	}

	/**
	 * Print a step of a statement, in the following form:
	 * <code>src->dst: statement at file:location text;</code>For example,<br>
	 * <code>32->17: sum = (sum+(3*i)) at f0:20.14-24 "sum += 3*i";</code><br>
	 * When the atomic lock variable is changed during executing the statement,
	 * then the corresponding information is printed as well. For example,<br>
	 * <code>13->6: ($ATOMIC_LOCK_VAR = $self) x = 0 at f0:30.17-22
	 "x = 0";</code>
	 * 
	 * @param s
	 *            The statement that has been executed in the current step.
	 * @param atomicKind
	 *            The atomic kind of the source location of the statement.
	 * @param atomCount
	 *            The atomic/atom count of the process that the statement
	 *            belongs to.
	 * @param atomicLockVarChanged
	 *            True iff the atomic lock variable is changed during the
	 *            execution of the statement.
	 * @throws UnsatisfiablePathConditionException
	 */
	private void printStatement(State currentState, State newState,
			Transition transition, AtomicKind atomicKind, int atomCount,
			boolean atomicLockVarChanged)
			throws UnsatisfiablePathConditionException {
		Statement stmt = transition.statement();
		config.out().print("  ");
		config.out().print(stmt.locationStepString());
		config.out().print(": ");
		config.out().print(
				symbolicAnalyzer.statementEvaluation(currentState, newState,
						transition.pid(), stmt));
		if (transition.transitionKind() == TransitionKind.NOOP) {
			NoopTransition noopTransition = (NoopTransition) transition;
			BooleanExpression assumption = noopTransition.assumption();

			if (assumption != null) {
				config.out().print(" [$assume(");
				config.out().print(
						symbolicAnalyzer.symbolicExpressionToString(stmt
								.getSource(), currentState,
								this.enabler.modelFactory.typeFactory()
										.booleanType(), assumption));
				config.out().print(")]");
			}
		}
		config.out().print(" at ");
		config.out().print(stmt.summaryOfSource());
		// config.out().print(
		// transition.statement().toStepString(atomicKind, atomCount,
		// atomicLockVarChanged));
		config.out().println();
	}

	/**
	 * Print the prefix of a transition.
	 * 
	 * @param printTransitions
	 *            True iff each step is to be printed.
	 * @param state
	 *            The source state of the transition.
	 * @param processIdentifier
	 *            The identifier of the process that this transition associates
	 *            with.
	 */
	private void printTransitionPrefix(State state, int processIdentifier) {
		// Executed by p0 from State 1
		config.out().print("Executed by p");
		config.out().println(processIdentifier + " from " + state + ":");
	}

	/**
	 * Print the updated status.
	 */
	private void printUpdateWork() {
		updater.print(config.out());
		config.out().flush();
	}

	/**
	 * Report error message for $atom block execution, when
	 * <ol>
	 * <li>non-determinism is detected, or</li>
	 * <li>a blocked location is encountered.</li>
	 * </ol>
	 * 
	 * @param kind
	 *            The status kind of the error.
	 * @param state
	 *            The state that the error occurs.
	 * @param location
	 *            The location that the error occurs.
	 * @throws UnsatisfiablePathConditionException
	 */
	private void reportErrorForAtom(EnabledStatus enabled, State state,
			Location location, String process)
			throws UnsatisfiablePathConditionException {
		switch (enabled) {
		case NONDETERMINISTIC:
			errorLogger.logSimpleError(location.getSource(), state, process,
					symbolicAnalyzer.stateInformation(state), ErrorKind.OTHER,
					"nondeterminism is encountered in $atom block.");
			throw new UnsatisfiablePathConditionException();
		case BLOCKED:
			errorLogger.logSimpleError(location.getSource(), state, process,
					symbolicAnalyzer.stateInformation(state), ErrorKind.OTHER,
					"blocked location is encountered in $atom block.");
			throw new UnsatisfiablePathConditionException();
		default:
		}
	}

	/* ********************* Methods from StateManagerIF ******************* */

	@Override
	public int getDepth(State state) {
		return state.getDepth();
	}

	@Override
	public TraceStepIF<Transition, State> nextState(State state,
			Transition transition) {
		TraceStepIF<Transition, State> result;

		// nextStateCalls++;
		try {
			result = nextStateWork(state, transition);
		} catch (UnsatisfiablePathConditionException e) {
			// problem is the interface requires an actual State
			// be returned. There is no concept of executing a
			// transition and getting null or an exception.
			// since the error has been logged, just return
			// some state with false path condition, so there
			// will be no next state...
			result = new NullTraceStep(state.setPathCondition(falseExpr));
		}
		return result;
	}

	@Override
	public boolean onStack(State state) {
		return state.onStack();
	}

	@Override
	public void printAllStatesLong(PrintStream arg0) {

	}

	@Override
	public void printAllStatesShort(PrintStream arg0) {

	}

	@Override
	public void printStateLong(PrintStream out, State state) {
		out.print(this.symbolicAnalyzer.stateToString(state));
	}

	@Override
	public void printStateShort(PrintStream out, State state) {
		out.print(state.toString());
	}

	@Override
	public void printTransitionLong(PrintStream out, Transition transition) {
		out.print(transition.toString());
	}

	@Override
	public void printTransitionShort(PrintStream out, Transition transition) {
		out.print(transition.toString());
	}

	@Override
	public boolean seen(State state) {
		return state.seen();
	}

	@Override
	public void setDepth(State state, int value) {
		state.setDepth(value);
	}

	@Override
	public void setOnStack(State state, boolean value) {
		state.setOnStack(value);
	}

	@Override
	public void setSeen(State state, boolean value) {
		state.setSeen(value);
	}

	/* ****************** Public Methods from StateManager ***************** */

	@Override
	public long getNumStateInstances() {
		return stateFactory.getNumStateInstances();
	}

	@Override
	public int getNumStatesSaved() {
		return stateFactory.getNumStatesSaved();
	}

	@Override
	public int maxProcs() {
		return maxProcs;
	}

	@Override
	public void printUpdate() {
		printUpdateWork();
	}

	@Override
	public void setUpdater(Printable updater) {
		this.updater = updater;
	}

	@Override
	public int numStatesExplored() {
		return numStatesExplored;
	}

	@Override
	public Map<BooleanExpression, Set<Pair<State, SymbolicExpression[]>>> collectedOutputs() {
		return this.outputCollector.collectedOutputs;
	}

	@Override
	public String[] outptutNames() {
		if (outputCollector != null)
			return this.outputCollector.outptutNames;
		return null;
	}

	@Override
	public void setStack(Stack<TransitionSequence> stack) {
		this.stack = stack;
	}
}
