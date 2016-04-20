package edu.udel.cis.vsl.civl.predicate.IF;

import edu.udel.cis.vsl.civl.log.IF.CIVLExecutionException;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.gmc.StatePredicateIF;

public interface CIVLStatePredicate extends StatePredicateIF<State> {

	CIVLExecutionException getViolation();

	/**
	 * Returns the violation that has not yet been reported.
	 * 
	 * @return
	 */
	CIVLExecutionException getUnreportedViolation();

	/**
	 * Is this an And predicate?
	 * 
	 * @return
	 */
	boolean isAndPredicate();
}
