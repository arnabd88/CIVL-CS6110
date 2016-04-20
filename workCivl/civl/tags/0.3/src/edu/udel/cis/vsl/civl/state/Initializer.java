package edu.udel.cis.vsl.civl.state;

import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;

public interface Initializer {

	/**
	 * Compute initial value of variable.  The state is the state
	 * before the variable is initialized.  Also need a PID which
	 * together with the state is needed to evaluate any array extent
	 * expressions occurring in the type of the variable.
	 * 
	 * Ultimately the PID is only needed for evaluating 'self'
	 * expressions.
	 * 
	 * 
	 * 
	 * @param state
	 * @param variable
	 * @param dynamicScopeId
	 * @return
	 */
	SymbolicExpression initialValue(State state, Variable variable,
			int dynamicScopeId);

}
