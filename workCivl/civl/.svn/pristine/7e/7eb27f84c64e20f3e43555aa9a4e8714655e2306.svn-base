package edu.udel.cis.vsl.civl.kripke;

import java.io.PrintStream;
import java.util.ArrayList;

import edu.udel.cis.vsl.civl.err.CIVLExecutionException;
import edu.udel.cis.vsl.civl.err.CIVLExecutionException.Certainty;
import edu.udel.cis.vsl.civl.err.CIVLExecutionException.ErrorKind;
import edu.udel.cis.vsl.civl.err.CIVLInternalException;
import edu.udel.cis.vsl.civl.err.CIVLStateException;
import edu.udel.cis.vsl.civl.err.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.SystemFunction;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.AssignStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.CallOrSpawnStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.ChooseStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.model.IF.statement.WaitStatement;
import edu.udel.cis.vsl.civl.model.common.statement.StatementList;
import edu.udel.cis.vsl.civl.semantics.Evaluation;
import edu.udel.cis.vsl.civl.semantics.Evaluator;
import edu.udel.cis.vsl.civl.semantics.Executor;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutor;
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
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;

/**
 * Enabler implements {@link EnablerIF} for CIVL models. It is an abstract class
 * and can have differernt sub classes for different implementation of reudction
 * techniques.
 * 
 * @author Manchun Zheng (zmanchun)
 * @author Timothy K. Zirkel (zirkel)
 */
public abstract class Enabler implements
		EnablerIF<State, Transition, TransitionSequence> {

	protected final String COMM_ENQUE = "$comm_enqueue";
	protected final String COMM_DEQUE = "$comm_dequeue";

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

	protected boolean showAmpleSet = false;;

	/**
	 * The unique transition factory used by the system.
	 */
	protected TransitionFactory transitionFactory;

	/**
	 * The unique symbolic universe used by the system.
	 */
	protected SymbolicUniverse universe;

	/* **************************** Public Methods ************************* */

	public BooleanExpression getGuard(Statement statement, int pid, State state) {
		Expression staticGuard;
		BooleanExpression guard = null;
		Evaluation eval;

		// calculate normal statement guards.
		staticGuard = statement.guard();
		try {
			eval = evaluator.evaluate(state, pid, staticGuard);
			state = eval.state;
			guard = (BooleanExpression) eval.value;
		} catch (UnsatisfiablePathConditionException e) {
			return universe.falseExpression();
		}
		// calculate the guard of system function calls.
		if (statement instanceof CallOrSpawnStatement
				&& ((CallOrSpawnStatement) statement).function() instanceof SystemFunction) {
			LibraryExecutor libExecutor = executor
					.libraryExecutor((CallOrSpawnStatement) statement);
			BooleanExpression systemGuard = libExecutor.getGuard(state, pid,
					(CallOrSpawnStatement) statement);

			if (guard != null)
				guard = universe.and(guard, systemGuard);
		} else {
			if (statement instanceof WaitStatement) {
				WaitStatement wait = (WaitStatement) statement;
				Expression waitExpr = wait.process();
				SymbolicExpression joinProcess;
				int pidValue;

				try {
					joinProcess = evaluator.evaluate(state, pid, waitExpr).value;
					pidValue = modelFactory.getProcessId(waitExpr.getSource(),
							joinProcess);
					if (!state.getProcessState(pidValue).hasEmptyStack())
						guard = universe.falseExpression();
				} catch (UnsatisfiablePathConditionException e) {
					return universe.falseExpression();
				}
			}
		}
		return guard;
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
		BooleanExpression guard = getGuard(statement, pid, state);
		BooleanExpression pathCondition = state.getPathCondition();
		Reasoner reasoner = evaluator.universe().reasoner(pathCondition);

		if (reasoner.isValid(guard))
			return pathCondition;
		if (reasoner.isValid(evaluator.universe().not(guard)))
			return evaluator.universe().falseExpression();
		return evaluator.universe().and(pathCondition, guard);
	}

	/* ************************ Methods from EnablerIF ********************* */

	@Override
	public TransitionSequence enabledTransitions(State state) {
		TransitionSequence transitions;
		if (state.getPathCondition().isFalse())
			// return empty set of transitions:
			return new TransitionSequence(state);

		transitions = enabledAtomicTransitions(state);
		if (transitions == null)
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
	ArrayList<SimpleTransition> enabledTransitionsOfStatement(State state,
			Statement s, BooleanExpression pathCondition, int pid,
			Statement assignAtomicLock) {
		ArrayList<SimpleTransition> localTransitions = new ArrayList<>();
		Statement transitionStatement;

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
							transitionStatement, universe.integer(i)));
				}
			} else if (s instanceof WaitStatement) {
				Evaluation eval = evaluator.evaluate(
						state.setPathCondition(pathCondition), pid,
						((WaitStatement) s).process());
				int pidValue = modelFactory.getProcessId(((WaitStatement) s)
						.process().getSource(), eval.value);

				if (pidValue < 0) {
					CIVLExecutionException e = new CIVLStateException(
							ErrorKind.INVALID_PID,
							Certainty.PROVEABLE,
							"Unable to call $wait on a process that has already been the target of a $wait.",
							state, s.getSource());

					evaluator.reportError(e);
					// TODO: recover: add a no-op transition
					throw e;
				}
				if (state.getProcessState(pidValue).hasEmptyStack()) {
					if (assignAtomicLock != null) {
						StatementList statementList = new StatementList(
								assignAtomicLock);

						statementList.add(s);
						transitionStatement = statementList;
					} else {
						transitionStatement = s;
					}
					localTransitions.add(transitionFactory.newSimpleTransition(
							pathCondition, pid, transitionStatement));
				}
			} else {
				if (assignAtomicLock != null) {
					StatementList statementList = new StatementList(
							assignAtomicLock);

					statementList.add(s);
					transitionStatement = statementList;
				} else {
					transitionStatement = s;
				}
				localTransitions.add(transitionFactory.newSimpleTransition(
						pathCondition, pid, transitionStatement));
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
	 * @return
	 */
	abstract TransitionSequence enabledTransitionsPOR(State state);

	/**
	 * Calculate the ID of the process that a given wait statement is waiting
	 * for.
	 * 
	 * @param state
	 *            The current state.
	 * @param p
	 *            The process that the wait statement belongs to.
	 * @param wait
	 *            The wait statement to be checked.
	 * @return The ID of the process that the wait statement is waiting for.
	 */
	int joinedIDofWait(State state, ProcessState p, WaitStatement wait) {
		Evaluation eval;
		try {
			eval = evaluator.evaluate(state, p.getPid(), wait.process());
			SymbolicExpression procVal = eval.value;

			return modelFactory.getProcessId(wait.process().getSource(),
					procVal);
		} catch (UnsatisfiablePathConditionException e) {
		}
		return -1;
	}

	/* **************************** Private Methods ************************ */

	private TransitionSequence enabledAtomicTransitions(State state) {
		TransitionSequence transitions;
		ArrayList<Integer> resumableProcesses;
		ProcessState p;
		AssignStatement assignStatement;
		Location pLocation;
		int pidInAtomic;

		pidInAtomic = executor.stateFactory().processInAtomic(state);
		if (pidInAtomic >= 0) {
			// execute a transition in an atomic block of a certain process
			// without interleaving with other processes
			TransitionSequence localTransitions = transitionFactory
					.newTransitionSequence(state);

			p = state.getProcessState(pidInAtomic);
			localTransitions.addAll(getTransitions(state, pidInAtomic, null));
			if (localTransitions.isEmpty()) {
				// release atomic lock if the current location of the process
				// that holds the lock is blocked
				state = executor.stateFactory().releaseAtomicLock(state);
			} else
				return localTransitions;
		}
		// TODO optimize the number of valid/prover calls
		resumableProcesses = executor.resumableAtomicProcesses(state);
		if (resumableProcesses.size() == 1) {
			int pid = resumableProcesses.get(0);

			p = state.getProcessState(pid);
			pLocation = p.getLocation();
			assignStatement = modelFactory.assignAtomicLockVariable(pid,
					pLocation);
			// only one process in atomic blocks could be resumed, so let
			// the process hold the atomic lock
			transitions = transitionFactory.newTransitionSequence(state);
			transitions.addAll(getTransitions(state, pid, assignStatement));
			if (transitions.isEmpty()) {
				throw new CIVLInternalException("unreachable", p.getLocation()
						.getSource());
			}
			return transitions;
		} else if (resumableProcesses.size() > 1) {
			// There are more than one processes trying to hold the atomic lock
			transitions = transitionFactory.newTransitionSequence(state);
			for (Integer pid : resumableProcesses) {
				pLocation = state.getProcessState(pid).getLocation();
				assignStatement = modelFactory.assignAtomicLockVariable(pid,
						pLocation);
				transitions.addAll(getTransitions(state, pid, assignStatement));
			}
			return transitions;
		} else {
			return null;
		}
	}

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
	private ArrayList<Transition> getTransitions(State state, int pid,
			Statement assignAtomicLock) {
		ProcessState p = state.getProcessState(pid);
		Location pLocation = p.getLocation();
		ArrayList<Transition> transitions = new ArrayList<>();

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
}
