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
	public boolean isCollective();

	/**
	 * @return The expression being checked.
	 */
	public Expression getExpression();

	/**
	 * @param isCollective
	 *            Whether this is a collective assertion.
	 */
	public void setCollective(boolean isCollective);

	/**
	 * @param expression
	 *            The expression being checked.
	 */
	public void setExpression(Expression expression);

}
