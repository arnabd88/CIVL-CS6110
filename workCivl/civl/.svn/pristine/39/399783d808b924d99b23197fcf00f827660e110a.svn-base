package edu.udel.cis.vsl.civl.semantics;

import edu.udel.cis.vsl.civl.state.State;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

/**
 * Represents the result of evaluating something that returns a symbolic type,
 * but in two parts: the (possibly) new state resulting from side-effects
 * arising from the evaluation, and the symbolic type resulting from the
 * evaluation.
 * 
 * @author siegel
 * 
 */
public class TypeEvaluation {

	public State state;

	public SymbolicType type;

	public TypeEvaluation(State state, SymbolicType type) {
		this.state = state;
		this.type = type;
	}

	@Override
	public String toString() {
		return "[" + state + ", " + type + "]";
	}

}
