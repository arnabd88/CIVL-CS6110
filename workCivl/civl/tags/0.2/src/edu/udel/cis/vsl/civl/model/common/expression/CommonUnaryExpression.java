/**
 * 
 */
package edu.udel.cis.vsl.civl.model.common.expression;

import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.UnaryExpression;

/**
 * A unary operation.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public class CommonUnaryExpression extends CommonExpression implements
		UnaryExpression {

	private UNARY_OPERATOR operator;
	private Expression operand;

	/**
	 * A unary operation.
	 * 
	 * @param operator
	 *            The unary operator.
	 * @param operand
	 *            The left operand.
	 */
	public CommonUnaryExpression(UNARY_OPERATOR operator, Expression operand) {
		this.operator = operator;
		this.operand = operand;
	}

	/**
	 * @return The binary operator
	 */
	public UNARY_OPERATOR operator() {
		return operator;
	}

	/**
	 * @return The operand.
	 */
	public Expression operand() {
		return operand;
	}

	/**
	 * @param operator
	 *            The unary operator.
	 */
	public void setOperator(UNARY_OPERATOR operator) {
		this.operator = operator;
	}

	/**
	 * @param operand
	 *            The operand.
	 */
	public void setOperand(Expression operand) {
		this.operand = operand;
	}

	@Override
	public String toString() {
		String op = "";

		switch (operator) {
		case NEGATIVE:
			op = "-";
			break;
		case NOT:
			op = "!";
			break;
		case ADDRESSOF:
			op = "&";
			break;
		case DEREFERENCE:
			op ="*";
			break;
		default:
			break;
		}
		return op + "(" + operand + ")";
	}

}
