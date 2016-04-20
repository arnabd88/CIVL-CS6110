/**
 * 
 */
package edu.udel.cis.vsl.civl.predicate.common;

import static edu.udel.cis.vsl.sarl.IF.ValidityResult.ResultType.MAYBE;
import static edu.udel.cis.vsl.sarl.IF.ValidityResult.ResultType.YES;
import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.kripke.IF.Enabler;
import edu.udel.cis.vsl.civl.kripke.IF.LibraryEnablerLoader;
import edu.udel.cis.vsl.civl.library.comm.LibcommEnabler;
import edu.udel.cis.vsl.civl.log.IF.CIVLExecutionException;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.Certainty;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.ErrorKind;
import edu.udel.cis.vsl.civl.model.IF.CIVLInternalException;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.CallOrSpawnStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement.StatementKind;
import edu.udel.cis.vsl.civl.predicate.IF.PotentialDeadlock;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluator;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryLoaderException;
import edu.udel.cis.vsl.civl.semantics.IF.SymbolicAnalyzer;
import edu.udel.cis.vsl.civl.state.IF.ProcessState;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.ValidityResult.ResultType;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;

/**
 * An potential deadlock occurs if all of the following hold:
 * 
 * <ol>
 * <li>not every process has terminated</li>
 * <li>the only enabled transitions are sends for which there is no matching
 * receive</li>
 * </ol>
 * 
 * @author Ziqing Luo
 */
public class CommonPotentialDeadlock extends CommonCIVLStatePredicate implements
		PotentialDeadlock {

	private Enabler enabler;

	private LibcommEnabler libEnabler;

	private BooleanExpression falseExpr;

	/**
	 * The symbolic analyzer for operations on symbolic expressions and states,
	 * used in this class for printing states.
	 */
	private SymbolicAnalyzer symbolicAnalyzer;

	/**
	 * 
	 * @param symbolicUniverse
	 *            The symbolic universe for creating symbolic expressions.
	 * @param enabler
	 *            The enabler of the system.
	 * @param symbolicAnalyzer
	 *            The symbolic analyzer used in the system.
	 * @throws LibraryLoaderException
	 */
	public CommonPotentialDeadlock(SymbolicUniverse symbolicUniverse,
			Enabler enabler, LibraryEnablerLoader loader, Evaluator evaluator,
			ModelFactory modelFactory, SymbolicUtility symbolicUtil,
			SymbolicAnalyzer symbolicAnalyzer) {
		this.universe = symbolicUniverse;
		this.falseExpr = symbolicUniverse.falseExpression();
		this.enabler = enabler;
		this.symbolicAnalyzer = symbolicAnalyzer;
		try {
			this.libEnabler = (LibcommEnabler) loader.getLibraryEnabler("comm",
					enabler, evaluator, modelFactory, symbolicUtil,
					symbolicAnalyzer);
		} catch (LibraryLoaderException e) {
			throw new CIVLInternalException(
					"PotentialDeadlock loads LibcommEnabler failed",
					(CIVLSource) null);
		}
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
			explanation.append("ProcessState " + pid + ": ");
			if (location == null) {
				explanation.append("terminated");
			} else {
				CIVLSource source = location.getSource();

				explanation.append("at location " + location.id() + ", ");
				if (source != null)
					explanation.append(source.getSummary());
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
					explanation.append("\n  Enabling predicate: " + predicate);
				}
			}
		}
		return explanation.toString();
	}

	@Override
	public String explanation() {
		if (violation == null)
			return "No any kind of deadlock";
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
			if (p == null || p.hasEmptyStack()) // p has terminated
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
				if (s.statementKind().equals(StatementKind.CALL_OR_SPAWN)) {
					CallOrSpawnStatement call = (CallOrSpawnStatement) s;

					// TODO: function pointer makes call.function() == null
					if (call.function() != null)
						if (call.function().name().name()
								.equals("$comm_enqueue")) {
							String process = "p" + p.identifier() + " (id = "
									+ pid + ")";
							BooleanExpression claim;

							claim = libEnabler.hasMatchedDequeue(state, pid,
									process, call, true);
							// TODO change to andTo
							guard = universe.and(guard, claim);
							predicate = universe.or(predicate, claim);
						}
				}
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
				message = "Cannot prove that potential or absolute deadlock is impossible:\n";
			} else {
				certainty = Certainty.PROVEABLE;
				message = "A potential or absolute deadlock is possible:\n";
			}
			message += "  Path condition: " + state.getPathCondition()
					+ "\n  Enabling predicate: " + predicate + "\n";
			message += explanationWork(state);
			violation = new CIVLExecutionException(ErrorKind.DEADLOCK,
					certainty, "", message,
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
		return "PotentialDeadlock";
	}

}
