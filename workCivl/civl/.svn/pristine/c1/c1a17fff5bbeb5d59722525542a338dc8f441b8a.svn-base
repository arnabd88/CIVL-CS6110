/**
 * 
 */
package edu.udel.cis.vsl.civl.model.common.expression;

import edu.udel.cis.vsl.civl.model.IF.expression.ArrayIndexExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;

/**
 * a[i], where "a" is an array and "i" is an expression evaluating to an
 * integer.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public class CommonArrayIndexExpression extends CommonExpression implements
		ArrayIndexExpression {

	private Expression array;
	private Expression index;

	/**
	 * a[i], where "a" is an array and "i" is an expression evaluating to an
	 * integer.
	 * 
	 * @param array
	 *            An expression evaluating to an array.
	 * @param index
	 *            An expression evaluating to an integer.
	 */
	public CommonArrayIndexExpression(Expression array, Expression index) {
		this.array = array;
		this.index = index;
	}

	/**
	 * @return The expression for the array.
	 */
	public Expression array() {
		return array;
	}

	/**
	 * @return The expression for the index.
	 */
	public Expression index() {
		return index;
	}

	/**
	 * @param array
	 *            The expression for the array.
	 */
	public void setArray(Expression array) {
		this.array = array;
	}

	/**
	 * @param index
	 *            The expression for the index.
	 */
	public void setIndex(Expression index) {
		this.index = index;
	}

	@Override
	public String toString() {
		return array + "[" + index + "]";
	}

}
