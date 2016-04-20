/**
 * 
 */
package edu.udel.cis.vsl.civl.model.IF.statement;

import edu.udel.cis.vsl.civl.model.IF.expression.Expression;

/**
 * An assert statement that checks if a given boolean expression is satisfied.
 * 
 * @author zirkel
 * 
 */
public interface AssertStatement extends Statement {

	/**
	 * @return The expression to be asserted.
	 */
	Expression getCondition();

	/**
	 * @param condition
	 *            The expression being added to the path condition.
	 */
	void setCondition(Expression condition);
	
	Expression[] getExplanation();

}
