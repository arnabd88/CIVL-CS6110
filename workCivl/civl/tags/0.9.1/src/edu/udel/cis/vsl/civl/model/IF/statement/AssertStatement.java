/**
 * 
 */
package edu.udel.cis.vsl.civl.model.IF.statement;

import edu.udel.cis.vsl.civl.model.IF.expression.Expression;

/**
 * An assert statement.
 * 
 * @author zirkel
 * 
 */
public interface AssertStatement extends Statement {

	/**
	 * @return Whether this is a collective assertion.
	 */
	boolean isCollective();

	/**
	 * @return The expression being checked.
	 */
	Expression getExpression();

	/**
	 * @param isCollective
	 *            Whether this is a collective assertion.
	 */
	void setCollective(boolean isCollective);

	/**
	 * @param expression
	 *            The expression being checked.
	 */
	void setExpression(Expression expression);

	Expression[] printfArguments();
}
