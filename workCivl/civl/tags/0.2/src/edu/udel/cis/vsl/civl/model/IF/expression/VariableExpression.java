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
public interface VariableExpression extends Expression {

	/**
	 * @return The variable
	 */
	public Variable variable();

	/**
	 * @param variable The variable.
	 */
	public void setVariable(Variable variable);
	
}
