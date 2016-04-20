/**
 * 
 */
package edu.udel.cis.vsl.civl.model.IF.statement;

import edu.udel.cis.vsl.civl.model.IF.expression.Expression;

/**
 * A return statement.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public interface ReturnStatement extends Statement {

	/**
	 * @return The expression being returned. Null if non-existent.
	 */
	Expression expression();

	/**
	 * @param expression
	 *            The expression being returned. Null if non-existent.
	 */
	void setExpression(Expression expression);

}
