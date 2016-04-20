/**
 * 
 */
package edu.udel.cis.vsl.civl.model.common.expression;

import edu.udel.cis.vsl.civl.model.IF.expression.CastExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.type.Type;

/**
 * A cast of an expression to a different type.
 * 
 * @author zirkel
 * 
 */
public class CommonCastExpression extends CommonExpression implements
		CastExpression {

	private Type type;
	private Expression expression;

	/**
	 * A cast of an expression to a different type.
	 * 
	 * @param type
	 *            The type to which the expression is cast.
	 * @param expression
	 *            The expression being cast to a new type.
	 */
	public CommonCastExpression(Type type, Expression expression) {
		this.type = type;
		this.expression = expression;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * edu.udel.cis.vsl.civl.model.IF.expression.CastExpression#getExpression()
	 */
	@Override
	public Expression getExpression() {
		return expression;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * edu.udel.cis.vsl.civl.model.IF.expression.CastExpression#getCastType()
	 */
	@Override
	public Type getCastType() {
		return type;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * edu.udel.cis.vsl.civl.model.IF.expression.CastExpression#setExpression
	 * (edu.udel.cis.vsl.civl.model.IF.expression.Expression)
	 */
	@Override
	public void setExpression(Expression expression) {
		this.expression = expression;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * edu.udel.cis.vsl.civl.model.IF.expression.CastExpression#setType(edu.
	 * udel.cis.vsl.civl.model.IF.type.Type)
	 */
	@Override
	public void setCastType(Type type) {
		this.type = type;
	}
	
	@Override
	public String toString() {
		return "(" + type + ") " + expression;
	}

}
