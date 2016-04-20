package edu.udel.cis.vsl.civl.semantics.IF;

import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;

/**
 * Represents the result of evaluating an expression in two parts: the
 * (possibly) new state resulting from side-effects arising from the evaluation,
 * and the value resulting from the evaluation.
 * 
 * @author siegel
 * 
 */
public class Evaluation {

	/* *************************** Instance Fields ************************* */
	/**
	 * The (possibly) new state resulting from side-effects arising from a
	 * certain evaluation.
	 */
	public State state;

	/**
	 * The value resulting from a certain evaluation.
	 */
	public SymbolicExpression value;

	/* ***************************** Constructors ************************** */

	/**
	 * Creates a new instance of evaluation.
	 * 
	 * @param state
	 *            The new state resulting from the evaluation.
	 * @param value
	 *            The value resulting from the evaluation.
	 */
	public Evaluation(State state, SymbolicExpression value) {
		this.state = state;
		this.value = value;
	}

	/* ************************ Methods from Object ************************ */

	@Override
	public String toString() {
		return "[" + state + ", " + value + "]";
	}

}
