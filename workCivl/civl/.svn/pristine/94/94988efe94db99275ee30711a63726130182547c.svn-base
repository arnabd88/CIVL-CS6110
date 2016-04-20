/**
 * 
 */
package edu.udel.cis.vsl.civl.model.common.expression;

import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;

/**
 * The parent of all expressions.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public class CommonExpression implements Expression {

	private Scope expressionScope = null;

	/**
	 * The parent of all expressions.
	 */
	public CommonExpression() {
	}

	/**
	 * @return The highest scope accessed by this expression. Null if no
	 *         variables accessed.
	 */
	public Scope expressionScope() {
		return expressionScope;
	}

	/**
	 * @param expressionScope
	 *            The highest scope accessed by this expression. Null if no
	 *            variables accessed.
	 */
	public void setExpressionScope(Scope expressionScope) {
		this.expressionScope = expressionScope;
	}

}
