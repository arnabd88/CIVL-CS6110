/**
 * 
 */
package edu.udel.cis.vsl.civl.predicate;

import edu.udel.cis.vsl.civl.log.ErrorLog;
import edu.udel.cis.vsl.civl.semantics.Evaluator;
import edu.udel.cis.vsl.civl.state.State;
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

	private ErrorLog log;
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
			Evaluator evaluator) {
		this.log = log;
		deadlockPredicate = new Deadlock(universe, evaluator);
	}

	@Override
	public String explanation() {
		return deadlockPredicate.explanation();
	}

	@Override
	public boolean holdsAt(State state) {
		if (log.numReports() >= log.errorBound()) {
			return true;
		}
		return deadlockPredicate.holdsAt(state);
	}

}
