package edu.udel.cis.vsl.civl.kripke;

import java.io.PrintStream;
import java.util.ArrayList;
import java.util.List;

import edu.udel.cis.vsl.civl.err.CIVLExecutionException;
import edu.udel.cis.vsl.civl.err.CIVLExecutionException.Certainty;
import edu.udel.cis.vsl.civl.err.CIVLExecutionException.ErrorKind;
import edu.udel.cis.vsl.civl.err.CIVLStateException;
import edu.udel.cis.vsl.civl.err.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.civl.library.IF.LibraryEnabler;
import edu.udel.cis.vsl.civl.library.IF.LibraryLoader;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.SystemFunction;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.CallOrSpawnStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.ChooseStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.model.IF.statement.WaitStatement;
import edu.udel.cis.vsl.civl.model.common.statement.StatementList;
import edu.udel.cis.vsl.civl.semantics.Evaluation;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluator;
import edu.udel.cis.vsl.civl.semantics.IF.Executor;
import edu.udel.cis.vsl.civl.state.IF.ProcessState;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.transition.SimpleTransition;
import edu.udel.cis.vsl.civl.transition.Transition;
import edu.udel.cis.vsl.civl.transition.TransitionFactory;
import edu.udel.cis.vsl.civl.transition.TransitionSequence;
import edu.udel.cis.vsl.gmc.EnablerIF;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;

/**
 * Enabler implements {@link EnablerIF} for CIVL models. It is an abstract class
 * and can have different implementations for different reduction techniques.
 * 
 * @author Manchun Zheng (zmanchun)
 * @author Timothy K. Zirkel (zirkel)
 */
public abstract class Enabler implements
		EnablerIF<State, Transition, TransitionSequence> {

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
	 * The unique executor used by the system.
	 */
	protected Executor executor;

	/**
	 * The unique model factory used by the system.
	 */
	protected ModelFactory modelFactory;

	/**
	 * The option to enable/disable the printing of ample sets of each state.
	 */
	protected boolean showAmpleSet = false;

	/**
	 * The unique transition factory used by the system.
	 */
	protected TransitionFactory transitionFactory;

	/**
	 * The unique symbolic universe used by the system.
	 */
	protected SymbolicUniverse universe;

	/**
	 * The symbolic expression for the boolean value false.
	 */
	protected BooleanExpression falseExpression;

	protected LibraryLoader libraryLoader;

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
	 * @param showAmpleSet
	 *            The option to enable or disable the printing of ample sets.
	 */
	protected Enabler(TransitionFactory transitionFactory, Evaluator evaluator,
			Executor executor, boolean showAmpleSet, LibraryLoader libLoader) {
		this.transitionFactory = transitionFactory;
		this.evaluator = evaluator;
		this.executor = executor;
		this.showAmpleSet = showAmpleSet;
		this.modelFactory = evaluator.modelFactory();
		this.universe = modelFactory.universe();
		falseExpression = universe.falseExpression();
		this.libraryLoader = libLoader;
	}

	/* **************************** Public Methods ************************* */

	/**
	 * Computes the guard of a statement. Since we have SystemGuardExpression
	 * and WaitGuardExpression, we don't need to compute the guard for system
	 * function calls and wait statements explicitly, which are now handled by
	 * the evaluator.
	 * 
	 * @param statement
	 *            The statement whose guard is to computed.
	 * @param pid
	 *            The ID of the process that the statement belongs to.
	 * @param state
	 *            The current state that the computation happens.
	 * @return The symbolic expression of the guard of the given statement.
	 */
	public Evaluation getGuard(Statement statement, int pid, State state) {
		// try {
		// if (statement instanceof CallOrSpawnStatement) {
		// if (((CallOrSpawnStatement) statement).isSystemCall()) {
		// return getSystemGuard(state, pid,
		// (CallOrSpawnStatement) statement);
		// }
		// }
		try {
			return evaluator.evaluate(state, pid, statement.guard());
		} catch (UnsatisfiablePathConditionException e) {
			return new Evaluation(state, this.falseExpression);
		}
		// } catch (UnsatisfiablePathConditionException e) {
		// return new Evaluation(state, this.falseExpression);
		// }
	}

	public Evaluation getSystemGuard(CIVLSource source, State state, int pid,
			String library, String function, List<Expression> arguments) {
		LibraryEnabler libEnabler = libraryEnabler(source, library);

		return libEnabler
				.evaluateGuard(source, state, pid, function, arguments);
	}

	private ArrayList<SimpleTransition> getEnabledTransitionsOfSystemCall(
			CIVLSource source, State state, CallOrSpawnStatement call,
			BooleanExpression pathCondition, int pid, int processIdentifier,
			Statement assignAtomicLock) {
		LibraryEnabler libEnabler = libraryEnabler(source,
				((SystemFunction) call.function()).getLibrary());

		return libEnabler.enabledTransitions(state, call, pathCondition, pid,
				processIdentifier, assignAtomicLock);
	}

	public LibraryEnabler libraryEnabler(CIVLSource civlSource, String library) {
		return this.libraryLoader.getLibraryEnabler(library, this,
				this.debugOut, evaluator.modelFactory());
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
	public BooleanExpression newPathCondition(State state, int pid,
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
		return universe.and(pathCondition, guard);
	}

	/**
	 * Returns the transition factory of this enabler.
	 * 
	 * @return
	 */
	public TransitionFactory transitionFactory() {
		return this.transitionFactory;
	}

	/* ************************ Methods from EnablerIF ********************* */

	@Override
	public TransitionSequence enabledTransitions(State state) {
		TransitionSequence transitions;

		if (state.getPathCondition().isFalse())
			// return empty set of transitions.
			return new TransitionSequence(state);
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
	ArrayList<Transition> enabledTransitionsOfProcess(State state, int pid) {
		ProcessState p = state.getProcessState(pid);
		Location pLocation = p.getLocation();
		ArrayList<Transition> transitions = new ArrayList<>();
		Statement assignAtomicLock = null;

		if (executor.stateFactory().processInAtomic(state) != pid
				&& p.atomicCount() > 0) {
			assignAtomicLock = modelFactory.assignAtomicLockVariable(pid,
					pLocation);
		}
		if (pLocation == null)
			return transitions;
		for (Statement s : pLocation.outgoing()) {
			BooleanExpression newPathCondition = newPathCondition(state, pid, s);

			if (!newPathCondition.isFalse()) {
				transitions.addAll(enabledTransitionsOfStatement(state, s,
						newPathCondition, pid, assignAtomicLock));
			}
		}
		return transitions;
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
	public ArrayList<SimpleTransition> enabledTransitionsOfStatement(
			State state, Statement s, BooleanExpression pathCondition, int pid,
			Statement assignAtomicLock) {
		ArrayList<SimpleTransition> localTransitions = new ArrayList<>();
		Statement transitionStatement = null;
		int processIdentifier = state.getProcessState(pid).identifier();

		try {
			if (s instanceof ChooseStatement) {
				Evaluation eval = evaluator.evaluate(
						state.setPathCondition(pathCondition), pid,
						((ChooseStatement) s).rhs());
				IntegerNumber upperNumber = (IntegerNumber) universe.reasoner(
						eval.state.getPathCondition()).extractNumber(
						(NumericExpression) eval.value);
				int upper;

				if (upperNumber == null)
					throw new CIVLStateException(ErrorKind.INTERNAL,
							Certainty.NONE,
							"Argument to $choose_int not concrete: "
									+ eval.value, eval.state, s.getSource());
				upper = upperNumber.intValue();
				if (assignAtomicLock != null) {
					transitionStatement = new StatementList(assignAtomicLock, s);
				} else {
					transitionStatement = s;
				}
				for (int i = 0; i < upper; i++) {
					localTransitions.add(transitionFactory.newChooseTransition(
							eval.state.getPathCondition(), pid,
							processIdentifier, transitionStatement,
							universe.integer(i)));
				}
			} else {
				if (s instanceof CallOrSpawnStatement) {
					CallOrSpawnStatement call = (CallOrSpawnStatement) s;

					// TODO think about optimization of system functions
					if (call.isSystemCall()) {// TODO check function pointer
						return this.getEnabledTransitionsOfSystemCall(
								call.getSource(), state, call, pathCondition,
								pid, processIdentifier, assignAtomicLock);
					} else {
						transitionStatement = s;
					}
				} else if (s instanceof WaitStatement) {
					Evaluation eval = evaluator.evaluate(
							state.setPathCondition(pathCondition), pid,
							((WaitStatement) s).process());
					int pidValue = modelFactory.getProcessId(
							((WaitStatement) s).process().getSource(),
							eval.value);

					if (pidValue < 0) {
						CIVLExecutionException e = new CIVLStateException(
								ErrorKind.INVALID_PID,
								Certainty.PROVEABLE,// TODO check message?
								"Unable to call $wait on a process that has already been the target of a $wait.",
								state, s.getSource());

						evaluator.reportError(e);
						// TODO: recover: add a no-op transition
						throw e;
					}
					if (state.getProcessState(pidValue).hasEmptyStack()) {
						transitionStatement = s;
					}
				} else {
					transitionStatement = s;
				}
				if (transitionStatement != null) {
					if (assignAtomicLock != null) {
						StatementList statementList = new StatementList(
								assignAtomicLock);

						statementList.add(s);
						transitionStatement = statementList;
					} else {
						transitionStatement = s;
					}
					localTransitions.add(transitionFactory.newSimpleTransition(
							pathCondition, pid, processIdentifier,
							transitionStatement));
				}
			}
		} catch (UnsatisfiablePathConditionException e) {
			// nothing to do: don't add this transition
		}
		return localTransitions;
	}

	/**
	 * Obtain enabled transitions with partial order reduction. May have
	 * different implementation of POR algorithms.
	 * 
	 * @param state
	 *            The current state.
	 * @return The enabled transitions computed by a certain POR approach.
	 */
	abstract TransitionSequence enabledTransitionsPOR(State state);

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
		// TransitionSequence transitions;
		// ArrayList<Integer> resumableProcesses;
		// AssignStatement assignStatement;
		// Location pLocation;
		int pidInAtomic;

		pidInAtomic = executor.stateFactory().processInAtomic(state);
		if (pidInAtomic >= 0) {
			// execute a transition in an atomic block of a certain process
			// without interleaving with other processes
			TransitionSequence localTransitions = transitionFactory
					.newTransitionSequence(state);

			localTransitions.addAll(enabledTransitionsOfProcess(state,
					pidInAtomic));
			if (localTransitions.isEmpty()) {
				// release atomic lock if the current location of the process
				// that holds the lock is blocked
				state = executor.stateFactory().releaseAtomicLock(state);
			} else
				return localTransitions;
		}
		return null;
		// // TODO optimize the number of valid/prover calls
		// resumableProcesses = executor.resumableAtomicProcesses(state);
		// if (resumableProcesses.size() == 1) {
		// int pid = resumableProcesses.get(0);
		//
		// p = state.getProcessState(pid);
		// pLocation = p.getLocation();
		// assignStatement = modelFactory.assignAtomicLockVariable(pid,
		// pLocation);
		// // only one process in atomic blocks could be resumed, so let
		// // the process hold the atomic lock
		// transitions = transitionFactory.newTransitionSequence(state);
		// transitions.addAll(enabledTransitionsOfProcess(state, pid,
		// assignStatement));
		// if (transitions.isEmpty()) {
		// throw new CIVLInternalException("unreachable", p.getLocation()
		// .getSource());
		// }
		// return transitions;
		// } else if (resumableProcesses.size() > 1) {
		// // There are more than one processes trying to hold the atomic lock
		// transitions = transitionFactory.newTransitionSequence(state);
		// for (Integer pid : resumableProcesses) {
		// pLocation = state.getProcessState(pid).getLocation();
		// assignStatement = modelFactory.assignAtomicLockVariable(pid,
		// pLocation);
		// transitions.addAll(enabledTransitionsOfProcess(state, pid,
		// assignStatement));
		// }
		// return transitions;
		// } else {
		// return null;
		// }
	}

	public Evaluator evaluator() {
		return this.evaluator;
	}
}
