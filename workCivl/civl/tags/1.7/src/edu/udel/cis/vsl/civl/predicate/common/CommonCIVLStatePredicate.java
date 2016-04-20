package edu.udel.cis.vsl.civl.predicate.common;

import edu.udel.cis.vsl.civl.log.IF.CIVLExecutionException;
import edu.udel.cis.vsl.civl.predicate.IF.CIVLStatePredicate;
import edu.udel.cis.vsl.civl.semantics.IF.SymbolicAnalyzer;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;

public abstract class CommonCIVLStatePredicate implements CIVLStatePredicate {

	/**
	 * If violation is found it is cached here.
	 */
	protected CIVLExecutionException violation = null;

	protected SymbolicUniverse universe;

	/**
	 * The symbolic analyzer for operations on symbolic expressions and states,
	 * used in this class for printing states.
	 */
	protected SymbolicAnalyzer symbolicAnalyzer;

	@Override
	public CIVLExecutionException getViolation() {
		return this.violation;
	}

	@Override
	public CIVLExecutionException getUnreportedViolation() {
		if (this.violation != null && !this.violation.isReported())
			return this.violation;
		return null;
	}

	@Override
	public boolean isAndPredicate() {
		return false;
	}
}
