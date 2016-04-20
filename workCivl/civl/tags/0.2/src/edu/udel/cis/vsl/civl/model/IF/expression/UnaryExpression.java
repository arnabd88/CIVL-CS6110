/**
 * 
 */
package edu.udel.cis.vsl.civl.model.IF.expression;

/**
 * A unary operation.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public interface UnaryExpression extends Expression {

	public enum UNARY_OPERATOR {
		NEGATIVE, NOT, ADDRESSOF, DEREFERENCE
	};

	/**
	 * @return The binary operator
	 */
	public UNARY_OPERATOR operator();

	/**
	 * @return The operand.
	 */
	public Expression operand();

	/**
	 * @param operator
	 *            The unary operator.
	 */
	public void setOperator(UNARY_OPERATOR operator);

	/**
	 * @param operand
	 *            The operand.
	 */
	public void setOperand(Expression operand);

}
