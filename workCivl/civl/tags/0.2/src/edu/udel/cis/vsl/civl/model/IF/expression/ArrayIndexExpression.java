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
public interface ArrayIndexExpression extends Expression {

	/**
	 * @return The expression for the array.
	 */
	public Expression array();

	/**
	 * @return The expression for the index.
	 */
	public Expression index();

	/**
	 * @param array
	 *            The expression for the array.
	 */
	public void setArray(Expression array);

	/**
	 * @param index
	 *            The expression for the index.
	 */
	public void setIndex(Expression index);

}
