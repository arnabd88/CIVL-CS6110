/**
 * 
 */
package edu.udel.cis.vsl.civl.predicate.IF;

import edu.udel.cis.vsl.civl.kripke.IF.Enabler;
import edu.udel.cis.vsl.civl.log.IF.CIVLExecutionException;
import edu.udel.cis.vsl.civl.semantics.IF.Executor;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.gmc.ErrorLog;
import edu.udel.cis.vsl.gmc.StatePredicateIF;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;

/**
 * The standard predicate checks for logged errors exceeding the error bound and
 * checks the deadlock predicate.
 * 
 * @author zirkel
 * 
 */
public class StandardPredicate implements StatePredicateIF<State> {

	// private ErrorLog log;
	private Deadlock deadlockPredicate;

	/**
	 * The standard predicate checks for logged errors exceeding the error bound
	 * and checks the deadlock predicate.
	 * 
	 * @param log
	 *            The error log.
	 * @param universe
	 *            The symbolic universe.
	 */
	public StandardPredicate(ErrorLog log, SymbolicUniverse universe,
			Enabler enabler, Executor executor) {
		deadlockPredicate = new Deadlock(universe, enabler, executor);
	}

	@Override
	public String explanation() {
		return deadlockPredicate.explanation();
	}

	public CIVLExecutionException getViolation() {
		return deadlockPredicate.getViolation();
	}

	@Override
	public boolean holdsAt(State state) {
		return deadlockPredicate.holdsAt(state);
	}

	@Override
	public String toString() {
		return "Deadlock";
	}

}
