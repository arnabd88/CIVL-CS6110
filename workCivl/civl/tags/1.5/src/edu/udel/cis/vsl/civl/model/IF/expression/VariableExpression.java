/**
 * 
 */
package edu.udel.cis.vsl.civl.model.IF.expression;

import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

/**
 * A use of a variable in an expression.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public interface VariableExpression extends LHSExpression {

	/**
	 * @return The variable
	 */
	Variable variable();

	/**
	 * @param variable
	 *            The variable.
	 */
	void setVariable(Variable variable);
}
