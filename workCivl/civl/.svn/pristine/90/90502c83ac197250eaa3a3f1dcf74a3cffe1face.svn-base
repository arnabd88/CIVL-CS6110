/**
 * 
 */
package edu.udel.cis.vsl.civl.model.common.expression;

import edu.udel.cis.vsl.civl.model.IF.expression.VariableExpression;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

/**
 * A use of a variable in an expression.
 * 
 * @author Timothy K. Zirkel (zirkel)
 *
 */
public class CommonVariableExpression extends CommonExpression implements VariableExpression {

	Variable variable;
	
	/**
	 * A use of a variable in an expression.
	 * 
	 * @param variable The variable.
	 */
	public CommonVariableExpression(Variable variable) {
		this.variable = variable;
	}

	/**
	 * @return The variable
	 */
	public Variable variable() {
		return variable;
	}

	/**
	 * @param variable The variable.
	 */
	public void setVariable(Variable variable) {
		this.variable = variable;
	}
	
	@Override
	public String toString() {
		return variable.name().name();
	}

}
