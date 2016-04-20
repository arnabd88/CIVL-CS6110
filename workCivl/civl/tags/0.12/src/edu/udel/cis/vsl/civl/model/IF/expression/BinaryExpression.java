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
		AND, LEFT_SHIFT, RIGHT_SHIFT, BITAND, BITCOMPLEMENT, BITOR,
		BITXOR, DIVIDE, EQUAL, IMPLIES, LESS_THAN, LESS_THAN_EQUAL, MINUS, MODULO, NOT_EQUAL, OR, 
		PLUS, POINTER_ADD, POINTER_SUBTRACT, SHIFTLEFT, SHIFTRIGHT, TIMES
	};

	/**
	 * @return The left operand.
	 */
	Expression left();

	/**
	 * @return The binary operator
	 */
	BINARY_OPERATOR operator();

	/**
	 * @return The right operand.
	 */
	Expression right();

	/**
	 * @param left
	 *            The left operand.
	 */
	void setLeft(Expression left);

	/**
	 * @param operator
	 *            The binary operator.
	 */
	void setOperator(BINARY_OPERATOR operator);

	/**
	 * @param right
	 *            The right operand.
	 */
	void setRight(Expression right);

}
