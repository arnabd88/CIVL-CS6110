/**
 * 
 */
package edu.udel.cis.vsl.civl.predicate.common;

import static edu.udel.cis.vsl.sarl.IF.ValidityResult.ResultType.MAYBE;
import static edu.udel.cis.vsl.sarl.IF.ValidityResult.ResultType.YES;
import edu.udel.cis.vsl.civl.kripke.IF.Enabler;
import edu.udel.cis.vsl.civl.log.IF.CIVLExecutionException;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.Certainty;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.ErrorKind;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.predicate.IF.Deadlock;
import edu.udel.cis.vsl.civl.semantics.IF.SymbolicAnalyzer;
import edu.udel.cis.vsl.civl.state.IF.ProcessState;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.ValidityResult.ResultType;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;

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
public class CommonDeadlock extends CommonCIVLStatePredicate implements
		Deadlock {

	private Enabler enabler;

	private BooleanExpression falseExpr;

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
	 * @param enabler
	 *            The enabler of the system.
	 * @param symbolicAnalyzer
	 *            The symbolic analyzer used in the system.
	 */
	public CommonDeadlock(SymbolicUniverse symbolicUniverse, Enabler enabler,
			SymbolicAnalyzer symbolicAnalyzer) {
		this.universe = symbolicUniverse;
		this.falseExpr = symbolicUniverse.falseExpression();
		this.enabler = enabler;
		this.symbolicAnalyzer = symbolicAnalyzer;
	}

	/**
	 * Precondition: already know that deadlock is a possibility in this state,
	 * i.e., we cannot show the enabled predicate is valid.
	 * 
	 * @param state
	 *            a state that might have a deadlock
	 * @return a String with a detailed explanation including the locatin of
	 *         each process in the state
	 * @throws UnsatisfiablePathConditionException
	 */
	private String explanationWork(State state)
			throws UnsatisfiablePathConditionException {
		StringBuffer explanation = new StringBuffer();
		boolean first = true;

		for (ProcessState p : state.getProcessStates()) {
			if (p == null)
				continue;

			Location location = null;
			BooleanExpression predicate = null;
			// wait on unterminated function, no outgoing edges:
			// String nonGuardExplanation = null;
			int pid = p.getPid();

			if (first)
				first = false;
			else
				explanation.append("\n");
			if (!p.hasEmptyStack())
				location = p.getLocation();
			explanation.append("process " + p.name() + " (id=" + pid + "): ");
			if (location == null) {
				explanation.append("terminated");
			} else {
				// CIVLSource source = location.getSource();

				// explanation.append("at location " + location.id() + ", ");
				// if (source != null)
				// explanation.append(source.getSummary());
				for (Statement statement : location.outgoing()) {
					BooleanExpression guard;

					guard = (BooleanExpression) enabler.getGuard(statement,
							pid, state).value;

					// if (statement instanceof WaitStatement) {
					// // TODO: Check that the guard is actually true, but it
					// // should be.
					// WaitStatement wait = (WaitStatement) statement;
					// Expression waitExpr = wait.process();
					// SymbolicExpression joinProcess = evaluator.evaluate(
					// state, pid, waitExpr).value;
					// int pidValue = modelFactory.getProcessId(
					// waitExpr.getSource(), joinProcess);
					// nonGuardExplanation = "\n  Waiting on process "
					// + pidValue;
					// }
					if (predicate == null) {
						predicate = guard;
					} else {
						predicate = universe.or(predicate, guard);
					}
				}
				if (predicate == null) {
					explanation.append("No outgoing transitions.");
					// } else if (nonGuardExplanation != null) {
					// explanation.append(nonGuardExplanation);
				} else {
					explanation.append(predicate);
				}
			}
		}
		return explanation.toString();
	}

	@Override
	public String explanation() {
		if (violation == null)
			return "No deadlock";
		return violation.getMessage();
	}

	private boolean allTerminated(State state) {
		for (ProcessState p : state.getProcessStates()) {
			if (p != null && !p.hasEmptyStack())
				return false;
		}
		return true;
	}

	private boolean holdsAtWork(State state)
			throws UnsatisfiablePathConditionException {
		if (allTerminated(state)) // all processes terminated: no deadlock.
			return false;

		BooleanExpression predicate = falseExpr;
		Reasoner reasoner = universe.reasoner(state.getPathCondition());
		CIVLSource source = null; // location of first non-term proc

		for (ProcessState p : state.getProcessStates()) {
			if (p == null || p.hasEmptyStack())
				continue;

			int pid = p.getPid();
			Location location = p.getLocation();

			if (source == null)
				source = location.getSource();
			for (Statement s : location.outgoing()) {
				BooleanExpression guard = (BooleanExpression) enabler.getGuard(
						s, pid, state).value;

				if (guard.isFalse())
					continue;
				predicate = universe.or(predicate, guard);
				if (predicate.isTrue())
					return false;
			} // end loop over all outgoing statements
		} // end loop over all processes

		ResultType enabled = reasoner.valid(predicate).getResultType();

		if (enabled == YES)
			return false;
		else {
			String message;
			Certainty certainty;

			if (enabled == MAYBE) {
				certainty = Certainty.MAYBE;
				message = "Cannot prove that deadlock is impossible:\n";
			} else {
				certainty = Certainty.PROVEABLE;
				message = "A deadlock is possible:\n";
			}
			message += "  Path condition: " + state.getPathCondition()
					+ "\n  Enabling predicate: " + predicate + "\n";
			message += explanationWork(state);
			violation = new CIVLExecutionException(ErrorKind.DEADLOCK,
					certainty, null, message,
					symbolicAnalyzer.stateInformation(state), source);
			return true;
		}
	}

	@Override
	public boolean holdsAt(State state) {
		try {
			return holdsAtWork(state);
		} catch (UnsatisfiablePathConditionException e) {
			return false;
		}
	}

	public String toString() {
		return "Deadlock";
	}

}
