package edu.udel.cis.vsl.civl.semantics;

import edu.udel.cis.vsl.civl.state.State;
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

	public State state;

	public SymbolicExpression value;

	public Evaluation(State state, SymbolicExpression value) {
		this.state = state;
		this.value = value;
	}

	@Override
	public String toString() {
		return "[" + state + ", " + value + "]";
	}

}
