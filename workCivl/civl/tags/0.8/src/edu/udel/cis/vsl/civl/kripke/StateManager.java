/**
 * 
 */
package edu.udel.cis.vsl.civl.kripke;

import java.io.PrintStream;

import edu.udel.cis.vsl.civl.err.CIVLExecutionException.Certainty;
import edu.udel.cis.vsl.civl.err.CIVLExecutionException.ErrorKind;
import edu.udel.cis.vsl.civl.err.CIVLInternalException;
import edu.udel.cis.vsl.civl.err.CIVLStateException;
import edu.udel.cis.vsl.civl.err.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.ChooseStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.model.common.location.CommonLocation.AtomicKind;
import edu.udel.cis.vsl.civl.model.common.statement.CommonNoopStatement;
import edu.udel.cis.vsl.civl.model.common.statement.StatementList;
import edu.udel.cis.vsl.civl.semantics.CommonExecutor.StateStatusKind;
import edu.udel.cis.vsl.civl.semantics.IF.Executor;
import edu.udel.cis.vsl.civl.state.IF.ProcessState;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.StateFactory;
import edu.udel.cis.vsl.civl.transition.ChooseTransition;
import edu.udel.cis.vsl.civl.transition.SimpleTransition;
import edu.udel.cis.vsl.civl.transition.Transition;
import edu.udel.cis.vsl.civl.util.Pair;
import edu.udel.cis.vsl.civl.util.Printable;
import edu.udel.cis.vsl.gmc.StateManagerIF;

/**
 * @author Timothy K. Zirkel (zirkel)
 * @author Manchun Zheng (zmanchun)
 * @author Stephen F. Siegel (siegel)
 * 
 */
public class StateManager implements StateManagerIF<State, Transition> {

	/* *************************** Instance Fields ************************* */

	/**
	 * The unique executor instance used by the system
	 */
	private Executor executor;

	/**
	 * The flag to turn on/off printing of debugging information.
	 */
	private boolean debug = false;

	/**
	 * The maximal number of processes at a state, initialized as 0.
	 */
	private int maxProcs = 0;

	/**
	 * The output stream to be used in this class to print states, transitions,
	 * warnings, etc.
	 */
	private PrintStream out = null;

	/**
	 * Save states during search?
	 * {@link edu.udel.cis.vsl.civl.run.UserInterface#saveStatesO}
	 */
	private boolean saveStates = true;

	/**
	 * Print saved states (i.e., canonicalized states)?
	 * {@link edu.udel.cis.vsl.civl.run.UserInterface#showSavedStatesO}
	 */
	private boolean showSavedStates = false;

	/**
	 * Print all states (including states that are not saved)?
	 * {@link edu.udel.cis.vsl.civl.run.UserInterface#showStatesO}
	 */
	private boolean showStates = false;

	/**
	 * Print transitions?
	 * {@link edu.udel.cis.vsl.civl.run.UserInterface#showTransitionsO}
	 */
	private boolean showTransitions = false;

	/**
	 * Simplify state returned by nextState?
	 * {@link edu.udel.cis.vsl.civl.run.UserInterface#simplifyO}
	 */
	private boolean simplify = true;

	/**
	 * The unique state factory used by the system.
	 */
	private StateFactory stateFactory;

	/**
	 * Turn on/off verbose mode.
	 * {@link edu.udel.cis.vsl.civl.run.UserInterface#verboseO}
	 */
	private boolean verbose = false;

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
	private boolean printUpdate = false;

	/**
	 * Number of calls to method {@link #nextState(State, Transition)}
	 */
	private int nextStateCalls = 0;

	/**
	 * Keep track of the maximal canonic ID of states. Since
	 * {@link StateFactory#canonic(State)} is only called when savedState option
	 * is enabled, this is only updated when savedState option is enabled. The
	 * motivation to have this field is to allow the state manager to print only
	 * new states in -savedStates mode, for better user experiences.
	 */
	private int maxCanonicId = -1;

	/* ***************************** Constructor *************************** */

	/**
	 * 
	 * @param executor
	 *            The unique executor to by used in the system.
	 */
	public StateManager(Executor executor) {
		this.executor = executor;
		this.stateFactory = executor.stateFactory();
	}

	/* *************************** Private Methods ************************* */

	/**
	 * Executes an $atom block, supporting nested atom blocks. It requires that
	 * the whole block is finite, non-blocking and deterministic. Otherwise, a
	 * warning or an error will be reported.
	 * 
	 * Precondition:
	 * <code> location.enterAtom() == true && location == state.getProcessState(pid).getLocation()</code>
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The id of the process being executing
	 * @param location
	 *            The start location of the atomic block
	 * @param print
	 *            True iff each step is to be printed.
	 * @return The resulting state after executing the $atom block
	 */
	private State executeAtomBlock(State state, int pid, Location location,
			boolean print) {
		ProcessState p;
		CIVLSource atomicStart = location.getSource();
		Location newLocation = location;
		State newState = state;
		int stateCounter = 0;
		int atomCount = 0;

		while (true) {
			boolean statementExecuted = false;
			State currentState = newState;
			Statement executedStatement = null;
			Pair<StateStatusKind, State> temp;

			for (Statement s : newLocation.outgoing()) {
				temp = executor.executeStatement(currentState, newLocation, s,
						pid);
				switch (temp.left) {
				case NONDETERMINISTIC:
					reportError(StateStatusKind.NONDETERMINISTIC, newState,
							newLocation);
					break;
				case NORMAL:
					if (statementExecuted) {
						reportError(StateStatusKind.NONDETERMINISTIC, newState,
								newLocation);
						break;
					}
					statementExecuted = true;
					newState = temp.right;
					executedStatement = s;
					break;
				default:// blocked, continue to try executing another
						// statement from the same location
					continue;
				}
			}
			// current location is blocked
			if (!statementExecuted) {
				reportError(StateStatusKind.BLOCKED, currentState, newLocation);
			}
			switch (newLocation.atomicKind()) {
			case ATOM_ENTER:
				atomCount++;
				break;
			case ATOM_EXIT:
				atomCount--;
			default:
			}
			if (atomCount == 0)// end of the $atom block
				return newState;
			// warning for possible infinite $atom block
			if (stateCounter != 0 && stateCounter % 1024 == 0) {
				out.println("Warning: " + (stateCounter)
						+ " states in $atom block at "
						+ atomicStart.getLocation() + ".");
			}
			stateCounter++;
			p = newState.getProcessState(pid);
			if (print && executedStatement != null) {
				printStatement(executedStatement, newLocation.atomicKind(),
						p.atomicCount(), false);
			}
			if (p != null && !p.hasEmptyStack())
				newLocation = p.getLocation();
			else {
				throw new CIVLInternalException("Unreachable",
						newLocation.getSource());
			}
		}
	}

	/**
	 * Execute the enabled statements from an ATOMIC_ENTER location of an
	 * $atomic block. When the process is already in atomic execution, i.e.,
	 * <code>p.inAtomic() == true</code>, then the atomic lock variable assign
	 * statement <code>$ATOMIC_LOCK_VAR = $self</code> is ignored.
	 * 
	 * @param pLocation
	 *            The location to work with.
	 * @param state
	 *            The current state.
	 * @param pid
	 *            The ID of the current executing process.
	 * @return A pair of the executed statement and the resulting state.
	 */
	private Pair<Statement, State> executeAtomicEnter(Location pLocation,
			State state, int pid) {
		State newState = state;
		ProcessState p = state.getProcessState(pid);
		Statement executedStatement;

		assert !stateFactory.lockedByAtomic(newState)
				|| stateFactory.processInAtomic(newState) == pid;
		executedStatement = pLocation.getOutgoing(0);
		if (!p.inAtomic()) {
			newState = executor.executeStatement(newState, pLocation,
					executedStatement, pid).right;
		} else {
			newState = stateFactory.setLocation(state, pid,
					executedStatement.target());
		}
		p = newState.getProcessState(pid).incrementAtomicCount();
		newState = stateFactory.setProcessState(newState, p, pid);
		return new Pair<Statement, State>(executedStatement, newState);
	}

	/**
	 * Execute the enabled statements from an ATOMIC_EXIT location of an $atomic
	 * block. When the process already finishes all active atomic execution,
	 * i.e., <code>p.inAtomic() == false</code>, then the atomic lock variable
	 * assign statement <code>$ATOMIC_LOCK_VAR = process<-1></code> will be
	 * executed; otherwise, it is merely ignored.
	 * 
	 * @param pLocation
	 *            The location to work with.
	 * @param state
	 *            The current state.
	 * @param pid
	 *            The ID of the current executing process.
	 * @param print
	 *            True iff each step is to be printed.
	 * @return A pair of the executed statement and the resulting state.
	 */
	private Pair<Statement, State> executeAtomicExit(Location pLocation,
			State state, int pid, boolean print) {
		State newState = state;
		ProcessState p;
		Statement executedStatement;

		assert stateFactory.processInAtomic(newState) == pid;
		p = newState.getProcessState(pid).decrementAtomicCount();
		newState = stateFactory.setProcessState(newState, p, pid);
		executedStatement = pLocation.getOutgoing(0);
		if (!p.inAtomic()) {
			newState = executor.executeStatement(newState, pLocation,
					pLocation.getOutgoing(0), pid).right;
			if (print) {
				printStatement(executedStatement, AtomicKind.ATOMIC_EXIT,
						p.atomicCount(), true);
			}
		} else
			newState = stateFactory.setLocation(newState, pid,
					executedStatement.target());
		return new Pair<Statement, State>(executedStatement, newState);
	}

	/**
	 * Execute the enabled statements from a normal location in an $atomic
	 * block. The result might be:
	 * <ol>
	 * <li>a sudo noop statement and the original state, when the location is
	 * non-deterministic;</li>
	 * <li>the unique statement that is enabled and the resulting state, when
	 * the location is deterministic and non-blocked; or</li>
	 * <li>NULL, when the location is blocked.</li>
	 * </ol>
	 * 
	 * @param pLocation
	 *            The location to work on.
	 * @param state
	 *            The current state.
	 * @param pid
	 *            The ID of the currently working process.
	 * @return A pair of the executed statement and the resulting state.
	 */
	private Pair<Statement, State> executeAtomicNormal(Location pLocation,
			State state, int pid) {
		State newState = state;
		Statement executedStatement = null;
		State oldState = newState;
		boolean executed = false;

		for (Statement s : pLocation.outgoing()) {
			Pair<StateStatusKind, State> temp = executor.executeStatement(
					oldState, pLocation, s, pid);

			switch (temp.left) {
			case NONDETERMINISTIC:
				// finds non-determinism, go back to previous state
				return new Pair<Statement, State>(new CommonNoopStatement(),
						oldState);
			case NORMAL:
				if (executed) {
					// finds non-determinism, go back to previous state
					return new Pair<Statement, State>(
							new CommonNoopStatement(), oldState);
				}
				executed = true;
				newState = temp.right;
				executedStatement = s;
				break;
			default:// BLOCKED, continue to try executing next statement
				continue;
			}
		}
		if (executedStatement != null)
			return new Pair<Statement, State>(executedStatement, newState);
		return null;
	}

	/**
	 * Execute a sequence of purely local statements or statements defined in an
	 * $atomic block of a certain process
	 * 
	 * @param state
	 *            The state to start with
	 * @param pid
	 *            id of the executing process
	 * @param location
	 *            The start location of the execution
	 * @param atomic
	 *            True iff executing statements in an atomic block; false iff
	 *            executing purely-local statements in non-atomic context.
	 * @param print
	 *            True iff each step is to be printed.
	 * @return The resulting state
	 */
	private State executeAtomicOrPurelyLocalStatements(State state, int pid,
			Location location, boolean atomic, boolean print) {
		Location pLocation = location;
		ProcessState p = state.getProcessState(pid);
		State newState = state;
		Statement executedStatement = null;
		boolean atomicLockVarChanged = false;
		Pair<Statement, State> oneStep;
		State oldState = null;
		boolean stepExecuted = false;

		assert atomic || pLocation.isPurelyLocal();
		while ((!atomic && pLocation != null && pLocation.isPurelyLocal())
				|| (atomic && pLocation != null)) {
			if (pLocation.isLoopPossible()) {
				return newState;
			}
			atomicLockVarChanged = false;
			oneStep = null;
			stepExecuted = true;
			switch (pLocation.atomicKind()) {
			case NONE:
				oldState = newState;
				oneStep = executeAtomicNormal(pLocation, newState, pid);
				break;
			case ATOM_ENTER:
				newState = executeAtomBlock(newState, pid, pLocation, print);
				stepExecuted = false;
				break;
			case ATOMIC_ENTER:
				if (atomic) {
					if (!p.inAtomic())
						atomicLockVarChanged = true;
					oneStep = executeAtomicEnter(pLocation, newState, pid);
				} else {
					newState = executeAtomicOrPurelyLocalStatements(newState,
							pid, pLocation, true, print);
					stepExecuted = false;
				}
				break;
			case ATOMIC_EXIT:
				if (!atomic)
					throw new CIVLInternalException("Unreachable",
							pLocation.getSource());
				oneStep = executeAtomicExit(pLocation, newState, pid, print);
				break;
			default:
				throw new CIVLInternalException("Unreachable",
						pLocation.getSource());
			}
			if (oneStep == null && stepExecuted) {
				// location is blocked
				if (atomic)
					oldState = stateFactory.releaseAtomicLock(oldState);
				if (print) {
					out.println("  " + pLocation.id()
							+ ": ($ATOMIC_LOCK_VAR = process<-1>) at "
							+ pLocation.getSource().getSummary() + ";");
				}
				return oldState;
			} else if (oneStep != null) {
				executedStatement = oneStep.left;
				newState = oneStep.right;
				// non-determinism
				if (newState == oldState)
					return oldState;
				if (atomic) {
					if (!newState.getProcessState(pid).inAtomic())
						return newState;
				}
			}
			p = newState.getProcessState(pid);
			if (p != null && print && stepExecuted) {
				printStatement(executedStatement, pLocation.atomicKind(),
						p.atomicCount(), atomicLockVarChanged);
			} else if (print && stepExecuted) {
				printStatement(executedStatement, pLocation.atomicKind(), 0,
						atomicLockVarChanged);
			}
			if (p != null && !p.hasEmptyStack())
				pLocation = p.peekStack().location();
			else
				pLocation = null;
		}
		return newState;
	}

	/**
	 * Execute a transition (obtained by the enabler) of a state. When the
	 * corresponding process is in atomic/atom execution, continue to execute
	 * more statements as many as possible. Also execute more purely local
	 * statements if possible.
	 * 
	 * @param state
	 *            The current state
	 * @param transition
	 *            The transition to be executed.
	 * @return the resulting state after execute
	 * @throws UnsatisfiablePathConditionException
	 */
	private State nextStateWork(State state, Transition transition)
			throws UnsatisfiablePathConditionException {
		int pid;
		Statement statement;
		int numProcs;
		ProcessState p;
		Location currentLocation;
		boolean printTransitions = verbose || debug || showTransitions;
		int oldMaxCanonicId = this.maxCanonicId;

		assert transition instanceof SimpleTransition;
		pid = ((SimpleTransition) transition).pid();
		p = state.getProcessState(pid);
		currentLocation = p.getLocation();
		switch (currentLocation.atomicKind()) {
		case ATOMIC_ENTER:
			printTransitionPrefix(printTransitions, state, pid);
			state = executeAtomicOrPurelyLocalStatements(state, pid,
					currentLocation, true, printTransitions);
			break;
		case ATOMIC_EXIT:
			printTransitionPrefix(printTransitions, state, pid);
			state = executeAtomicOrPurelyLocalStatements(state, pid,
					currentLocation, true, printTransitions);
			break;
		case ATOM_ENTER:
			printTransitionPrefix(printTransitions, state, pid);
			state = executeAtomBlock(state, pid, currentLocation,
					printTransitions);
			break;
		case ATOM_EXIT:
			throw new CIVLInternalException("Unreachable",
					currentLocation.getSource());
		default:// execute a normal transition
			if (printTransitions) {
				out.print(state + ", ");
				printTransitionLong(out, transition);
			}
			state = state.setPathCondition(((SimpleTransition) transition)
					.pathCondition());
			statement = ((SimpleTransition) transition).statement();
			if (transition instanceof ChooseTransition) {
				if (statement instanceof StatementList) {
					state = executor.executeStatementList(state, pid,
							(StatementList) statement,
							((ChooseTransition) transition).value());
				} else {
					assert statement instanceof ChooseStatement;
					state = executor.executeChoose(state, pid,
							(ChooseStatement) statement,
							((ChooseTransition) transition).value());
				}
			} else {
				state = executor.execute(state, pid, statement);
			}
			// sometimes the execution might allow the process to grab the
			// atomic lock
			if (executor.stateFactory().lockedByAtomic(state)) {
				currentLocation = state.getProcessState(pid).getLocation();
				state = executeAtomicOrPurelyLocalStatements(state, pid,
						currentLocation, true, printTransitions);
			}
		}
		// do nothing when process pid terminates and is removed from the state
		if (!stateFactory.lockedByAtomic(state) && state.numProcs() > pid) {
			p = state.getProcessState(pid);
			if (p != null && !p.hasEmptyStack()) {
				Location newLocation = p.peekStack().location();

				// execute purely local statements of the current process
				// greedily
				if (newLocation != null && newLocation.isPurelyLocal()) {
					state = executeAtomicOrPurelyLocalStatements(state, pid,
							newLocation, false, printTransitions);
				}
			}
		}
		if (printTransitions) {
			out.print("--> ");
		}
		if (saveStates) {
			state = stateFactory.canonic(state);
			this.maxCanonicId = state.getCanonicId();
		} else {
			state = stateFactory.collectProcesses(state);
			state = stateFactory.collectScopes(state);
			state.commit();
		}
		if (verbose || debug || showTransitions) {
			out.println(state);
		}
		if (debug
				|| verbose
				|| (!saveStates && showStates)
				|| (saveStates && showStates && this.maxCanonicId > oldMaxCanonicId)
				|| (saveStates && showSavedStates && this.maxCanonicId > oldMaxCanonicId)) {
			// in -savedStates mode, only print new states.
			out.println();
			state.print(out);
		}
		numProcs = state.numProcs();
		if (numProcs > maxProcs)
			maxProcs = numProcs;
		return state;
	}

	/**
	 * Print a step of a statement, in the following form:
	 * <code>src->dst: statement at file:location text;</code>For example,<br>
	 * <code>32->17: sum = (sum+(3*i)) at f0:20.14-24 "sum += 3*i";</code><br>
	 * When the atomic lock variable is changed during executing the statement,
	 * then the corresponding information is printed as well. For example,<br>
	 * <code>13->6: ($ATOMIC_LOCK_VAR = $self) x = 0 at f0:30.17-22 "x = 0";</code>
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
	 */
	private void printStatement(Statement s, AtomicKind atomicKind,
			int atomCount, boolean atomicLockVarChanged) {
		out.print(s.toStepString(atomicKind, atomCount, atomicLockVarChanged));
	}

	/**
	 * Print the prefix of a transition.
	 * 
	 * @param printTransitions
	 *            True iff each step is to be printed.
	 * @param state
	 *            The source state of the transition.
	 * @param pid
	 *            The ID of the process that this transition associates with.
	 */
	private void printTransitionPrefix(boolean printTransitions, State state,
			int pid) {
		if (printTransitions) {
			out.print(state + ", proc ");
			out.println(pid + ":");
		}
	}

	/**
	 * Print the updated status.
	 */
	private void printUpdateWork() {
		updater.print(out);
		out.flush();
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
	 */
	private void reportError(StateStatusKind kind, State state,
			Location location) {
		switch (kind) {
		case NONDETERMINISTIC:
			executor.evaluator().reportError(
					new CIVLStateException(ErrorKind.OTHER, Certainty.CONCRETE,
							"Non-determinism is encountered in $atom block.",
							state, location.getSource()));
			break;
		case BLOCKED:
			executor.evaluator().reportError(
					new CIVLStateException(ErrorKind.OTHER, Certainty.CONCRETE,
							"Blocked location is encountered in $atom block.",
							state, location.getSource()));
			break;
		default:
		}
	}

	/*********************** Methods from StateManagerIF *********************/

	@Override
	public int getDepth(State state) {
		return state.getDepth();
	}

	@Override
	public State nextState(State state, Transition transition) {
		nextStateCalls++;
		if (nextStateCalls % 100 == 0) {
			synchronized (this) {
				if (printUpdate) {
					printUpdateWork();
					printUpdate = false;
				}
			}
		}
		try {
			return nextStateWork(state, transition);
		} catch (UnsatisfiablePathConditionException e) {
			// problem is the interface requires an actual State
			// be returned. There is no concept of executing a
			// transition and getting null or an exception.
			// since the error has been logged, just stutter:
			return state;
		}

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
		state.print(out);
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

	/************************** Other Public Methods *************************/

	/**
	 * 
	 * @return the debugging option, true if under debug mode, otherwise false.
	 */
	public boolean getDebug() {
		return debug;
	}

	/**
	 * Returns the number of objects of type State that have been instantiated
	 * since this JVM started.
	 * 
	 * @return the number of states instantiated
	 */
	public long getNumStateInstances() {
		return stateFactory.getNumStateInstances();
	}

	/**
	 * Returns the number of states saved, i.e., made canonic.
	 * 
	 * @return the number of canonic states
	 */
	public int getNumStatesSaved() {
		return stateFactory.getNumStatesSaved();
	}

	/**
	 * The whole system should be using the same print stream to print
	 * information in different components.
	 * 
	 * @return the output stream used by the state manager
	 */
	public PrintStream getOutputStream() {
		return out;
	}

	/**
	 * -saveStates is always true in depth first search.
	 * 
	 * @return the value of the option -saveStates
	 */
	public boolean getSaveStates() {
		return saveStates;
	}

	/**
	 * -showSavedStates is false by default
	 * 
	 * @return the value of the option -showSavedStates
	 */
	public boolean getShowSavedStates() {
		return showSavedStates;
	}

	/**
	 * -showStates is false by default
	 * 
	 * @return the value of the option -showStates
	 */
	public boolean getShowStates() {
		return showStates;
	}

	/**
	 * -showTransitions is false by default
	 * 
	 * @return the value of the option -showTransitions
	 */
	public boolean getShowTransitions() {
		return showTransitions;
	}

	/**
	 * -simplify is true by default
	 * 
	 * @return the value of the option -simplify
	 */
	public boolean getSimplify() {
		return simplify;
	}

	/**
	 * The updater, see also {@link #updater}.
	 * 
	 * @return the updater.
	 */
	public Printable getUpdater() {
		return updater;
	}

	/**
	 * -verbose is false by default
	 * 
	 * @return the value of the option -verbose
	 */
	public boolean getVerbose() {
		return verbose;
	}

	/**
	 * @return The maximum number of processes in any state encountered by this
	 *         state manager.
	 */
	public int maxProcs() {
		return maxProcs;
	}

	/**
	 * Set the field debug.
	 * 
	 * @param value
	 *            The value to be used.
	 */
	public void setDebug(boolean value) {
		this.debug = value;
	}

	/**
	 * Set the field savedStates.
	 * 
	 * @param value
	 *            The value to be used.
	 */
	public void setSaveStates(boolean value) {
		this.saveStates = value;
	}

	/**
	 * Set the field showSavedStates.
	 * 
	 * @param value
	 *            The value to be used.
	 */
	public void setShowSavedStates(boolean value) {
		this.showSavedStates = value;
	}

	/**
	 * Set the field showStates.
	 * 
	 * @param value
	 *            The value to be used.
	 */
	public void setShowStates(boolean value) {
		this.showStates = value;
	}

	/**
	 * Set the field showTransitions.
	 * 
	 * @param value
	 *            The value to be used.
	 */
	public void setShowTransitions(boolean value) {
		this.showTransitions = value;
	}

	/**
	 * Set the field simplify.
	 * 
	 * @param value
	 *            The value to be used.
	 */
	public void setSimplify(boolean value) {
		simplify = value;
	}

	/**
	 * Set the field savedStates.
	 * 
	 * @param updater
	 *            The value to be used.
	 */
	public void setUpdater(Printable updater) {
		this.updater = updater;
	}

	/**
	 * Set the field out.
	 * 
	 * @param out
	 *            The output stream to be used.
	 */
	public void setOutputStream(PrintStream out) {
		this.out = out;
	}

	/**
	 * Set the field verbose.
	 * 
	 * @param value
	 *            The value to be used.
	 */
	public void setVerbose(boolean value) {
		this.verbose = value;
	}

	/**
	 * Print an update message at your earliest possible convenience.
	 */
	public synchronized void printUpdate() {
		printUpdate = true;
	}

}
