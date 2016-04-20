/**
 * 
 */
package edu.udel.cis.vsl.civl.model.common.expression;

import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.type.Type;

/**
 * The parent of all expressions.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public class CommonExpression implements Expression {

	private Scope expressionScope = null;
	protected Type expressionType = null;

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

	@Override
	public Type getExpressionType() {
		return expressionType;
	}

	/**
	 * 
	 * @param expressionType
	 *            The type resulting from this expression.
	 */
	public void setExpressionType(Type expressionType) {
		this.expressionType = expressionType;
	}

}
