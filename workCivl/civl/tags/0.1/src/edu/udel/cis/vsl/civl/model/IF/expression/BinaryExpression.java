/**
 * 
 */
package edu.udel.cis.vsl.civl.model.IF.expression;

/**
 * A binary operation.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public interface BinaryExpression extends Expression {

	public enum BINARY_OPERATOR {
		PLUS, 
		MINUS, 
		TIMES, 
		DIVIDE, 
		LESS_THAN, 
		LESS_THAN_EQUAL, 
		EQUAL, NOT_EQUAL, 
		AND, 
		OR, 
		MODULO
	};

	/**
	 * @return The binary operator
	 */
	public BINARY_OPERATOR operator();

	/**
	 * @return The left operand.
	 */
	public Expression left();

	/**
	 * @return The right operand.
	 */
	public Expression right();

	/**
	 * @param operator
	 *            The binary operator.
	 */
	public void setOperator(BINARY_OPERATOR operator);

	/**
	 * @param left
	 *            The left operand.
	 */
	public void setLeft(Expression left);

	/**
	 * @param right
	 *            The right operand.
	 */
	public void setRight(Expression right);

}
