/**
 * 
 */
package edu.udel.cis.vsl.civl.model.IF.statement;

import edu.udel.cis.vsl.civl.model.IF.expression.Expression;

/**
 * An assume statement provides an expression which is to be added to the path
 * condition.
 * 
 * @author zirkel
 * 
 */
public interface AssumeStatement extends Statement {

	/**
	 * @return The expression being added to the path condition.
	 */
	public Expression getExpression();

	/**
	 * @param expression
	 *            The expression being added to the path condition.
	 */
	public void setExpression(Expression expression);

}
