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
		NEGATIVE, NOT, BIG_O
	};

	/**
	 * @return The binary operator
	 */
	UNARY_OPERATOR operator();
	
	String operatorToString();

	/**
	 * @return The operand.
	 */
	Expression operand();

	/**
	 * @param operator
	 *            The unary operator.
	 */
	void setOperator(UNARY_OPERATOR operator);

	/**
	 * @param operand
	 *            The operand.
	 */
	void setOperand(Expression operand);

}
