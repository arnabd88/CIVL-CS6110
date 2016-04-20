package edu.udel.cis.vsl.civl.model.IF;

import edu.udel.cis.vsl.civl.model.IF.expression.Expression;

/**
 * An accuracy assumption builder provides logic for determining additional
 * assumptions that should be added after an assumption involving an abstract
 * function call.
 * 
 * @author zirkel
 * 
 */
public interface AccuracyAssumptionBuilder {

	/**
	 * Analyze an assumption. If that assumption contains an abstract function
	 * call, use heuristics to come up with appropriate Taylor series expansions
	 * when possible. Return these as a fragment of code consisting of
	 * additional assumptions.
	 * 
	 * @param assumption
	 *            The expression being added to the path condition.
	 * @param scope
	 *            The scope containing the expression.
	 * @return A fragment (possibly empty) with assumptions relating to Taylor
	 *         expansions of any abstract functions that are called within the
	 *         assumption.
	 */
	Fragment accuracyAssumptions(Expression assumption, Scope scope);

}
