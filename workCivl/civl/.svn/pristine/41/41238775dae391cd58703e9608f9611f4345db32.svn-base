/**
 * 
 */
package edu.udel.cis.vsl.civl.predicate;

import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.JoinStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.semantics.Evaluator;
import edu.udel.cis.vsl.civl.state.Process;
import edu.udel.cis.vsl.civl.state.State;
import edu.udel.cis.vsl.civl.util.ExecutionProblem.Certainty;
import edu.udel.cis.vsl.gmc.StatePredicateIF;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.ValidityResult;
import edu.udel.cis.vsl.sarl.IF.ValidityResult.ResultType;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;

/**
 * An absolute deadlock occurs if all of the following hold:
 * 
 * <ol>
 * <li>not every process has terminated
 * <li>no process has an enabled statement (note that a send statement is
 * enabled iff the current number of buffered messages is less than the buffer
 * bound).
 * </ol>
 * 
 * It is to be contrasted with a "potentially deadlocked" state, i.e., one in
 * which there may be send transitions enabled, but the send transitions can
 * only execute if buffering is allowed, i.e., no matching receives are
 * currently posted. Every absolutely deadlocked state is potentially
 * deadlocked, but not necessarily vice-versa.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public class Deadlock implements StatePredicateIF<State> {

	private SymbolicUniverse symbolicUniverse;
	private Evaluator evaluator;
	private String pidPrefix = "PID_";

	/**
	 * If the property holds (i.e., a deadlock has been detected at state), than
	 * the state is stored in this variable for future reference so that a nice
	 * "explanation" can be presented to the user.
	 */
	private State holdState = null;

	/**
	 * An absolute deadlock occurs if all of the following hold:
	 * 
	 * <ol>
	 * <li>not every process has terminated
	 * <li>no process has an enabled statement (note that a send statement is
	 * enabled iff the current number of buffered messages is less than the
	 * buffer bound).
	 * </ol>
	 * 
	 * It is to be contrasted with a "potentially deadlocked" state, i.e., one
	 * in which there may be send transitions enabled, but the send transitions
	 * can only execute if buffering is allowed, i.e., no matching receives are
	 * currently posted. Every absolutely deadlocked state is potentially
	 * deadlocked, but not necessarily vice-versa.
	 * 
	 * @param symbolicUniverse
	 *            The symbolic universe for creating symbolic expressions.
	 * @param evaluator
	 *            The evaluator to get symbolic expressions for values in a
	 *            given state.
	 * @param prover
	 *            The theorem prover to check validity of statement guards under
	 *            the path condition.
	 */
	public Deadlock(SymbolicUniverse symbolicUniverse, Evaluator evaluator) {
		this.symbolicUniverse = symbolicUniverse;
		this.evaluator = evaluator;
	}

	@Override
	public String explanation() {
		State state = holdState;
		String explanation;

		if (state == null) {
			return "No deadlock possible at this state.";
		}
		explanation = "\n*****************************************************************\n"
				// +
				// "*                                                                                  *\n"
				+ "  Deadlock possible at "
				+ state
				+ "!\n"
				// +
				// "*                                                                              *\n"
				+ "*****************************************************************\n";
		for (Process p : state.processes()) {
			Location location = null;
			SymbolicExpression predicate = null;
			String nonGuardExplanation = null; // Join of unterminated function,
												// etc.

			if (p == null) {
				continue;
			}
			if (!p.hasEmptyStack()) {
				location = p.location();
			}
			explanation += "Process " + p.id() + ": ";
			if (location == null) {
				explanation += "terminated\n";
			} else {
				explanation += "at location " + location.id() + ". ";
				for (Statement statement : location.outgoing()) {
					SymbolicExpression guard = evaluator.evaluate(state,
							p.id(), statement.guard());

					if (statement instanceof JoinStatement) {
						// TODO: Check that the guard is actually true, but it
						// should be.
						nonGuardExplanation = "Target process has not terminated:\n"
								+ ((JoinStatement) statement).process() + "\n";
					}
					if (predicate == null) {
						predicate = guard;
					} else {
						predicate = symbolicUniverse.or(
								(BooleanExpression) predicate,
								(BooleanExpression) guard);
					}
				}
				if (predicate == null) {
					explanation += "No outgoing transitions.\n";
				} else if (nonGuardExplanation != null) {
					explanation += nonGuardExplanation;
				} else {
					explanation += "Cannot prove enabling statement valid:\n"
							+ predicate + "\n";
				}
			}
		}
		return explanation;
	}

	@Override
	public boolean holdsAt(State state) {
		Certainty certainty = Certainty.PROVEABLE;
		String message;
		boolean terminated = true;

		for (Process p : state.processes()) {
			if (!p.hasEmptyStack()) {
				terminated = false;
				break;
			}
		}
		if (terminated) { // all processes terminated: no deadlock.
			return false;
		}
		for (Process p : state.processes()) {
			Location location;
			ValidityResult truth;
			SymbolicExpression predicate = null;

			// If a process has an empty stack, it can't execute.
			if (p == null || p.hasEmptyStack()) {
				continue;
			}
			location = p.location();
			for (Statement s : location.outgoing()) {
				if (s instanceof JoinStatement) {
					SymbolicExpression joinProcess = evaluator.evaluate(state,
							p.id(), ((JoinStatement) s).process());
					int pidValue;
					SymbolicExpression guard = evaluator.evaluate(state,
							p.id(), s.guard());

					// If guard is false, don't worry about the stack.
					if (guard.equals(symbolicUniverse.falseExpression())) {
						continue;
					}
					assert joinProcess instanceof SymbolicConstant;
					assert ((SymbolicConstant) joinProcess).name().getString()
							.startsWith(pidPrefix);
					// TODO: Throw exception if not the right type.
					pidValue = Integer
							.parseInt(((SymbolicConstant) joinProcess).name()
									.getString().substring(pidPrefix.length()));
					if (state.process(pidValue).hasEmptyStack()) {
						return false;
					}
				} else {
					SymbolicExpression guard = evaluator.evaluate(state,
							p.id(), s.guard());
					Reasoner reasoner = symbolicUniverse
							.reasoner((BooleanExpression) (state
									.pathCondition()));

					// Most of the time, guards will be true. Shortcut this.
					if (guard.equals(symbolicUniverse.trueExpression())) {
						return false;
					}
					if (predicate == null) {
						predicate = guard;
					} else {
						predicate = symbolicUniverse.or(
								(BooleanExpression) predicate,
								(BooleanExpression) guard);
					}
					truth = reasoner.valid((BooleanExpression) predicate);
					if (truth.getResultType() == ResultType.YES) {
						return false;
					} else if (truth.getResultType() == ResultType.MAYBE) {
						certainty = Certainty.MAYBE;
					} else {
						// For some input, no statement is enabled for this
						// process.
					}
				}
			}
		}
		// If we're here, deadlock might be possible.
		holdState = state;
		if (certainty == Certainty.MAYBE) {
			message = "Cannot prove that deadlock is impossible:";
		} else {
			message = "A deadlock is possible:";
		}
		message += explanation();
		System.out.println(message);
		state.print(System.out);
		return true;
	}

	public String toString() {
		return "Deadlock";
	}

}
