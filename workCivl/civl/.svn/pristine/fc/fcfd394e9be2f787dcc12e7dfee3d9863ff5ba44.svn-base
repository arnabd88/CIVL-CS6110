/**
 * 
 */
package edu.udel.cis.vsl.civl.model.IF.expression;

/**
 * a[i], where "a" is an array and "i" is an expression evaluating to an
 * integer.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public interface SubscriptExpression extends LHSExpression {

	/**
	 * @return The expression for the array.
	 */
	LHSExpression array();

	/**
	 * @return The expression for the index.
	 */
	Expression index();

	/**
	 * @param array
	 *            The expression for the array.
	 */
	void setArray(LHSExpression array);

	/**
	 * @param index
	 *            The expression for the index.
	 */
	void setIndex(Expression index);

}
