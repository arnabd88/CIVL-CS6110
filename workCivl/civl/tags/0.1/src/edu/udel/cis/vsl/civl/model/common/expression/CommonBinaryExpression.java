/**
 * 
 */
package edu.udel.cis.vsl.civl.model.common.expression;

import edu.udel.cis.vsl.civl.model.IF.expression.BinaryExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;

/**
 * A binary operation.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public class CommonBinaryExpression extends CommonExpression implements
		BinaryExpression {

	private BINARY_OPERATOR operator;
	private Expression left;
	private Expression right;

	/**
	 * A binary operation.
	 * 
	 * @param operator
	 *            The binary operator.
	 * @param left
	 *            The left operand.
	 * @param right
	 *            The right operand.
	 */
	public CommonBinaryExpression(BINARY_OPERATOR operator, Expression left,
			Expression right) {
		this.operator = operator;
		this.left = left;
		this.right = right;
	}

	/**
	 * @return The binary operator
	 */
	public BINARY_OPERATOR operator() {
		return operator;
	}

	/**
	 * @return The left operand.
	 */
	public Expression left() {
		return left;
	}

	/**
	 * @return The right operand.
	 */
	public Expression right() {
		return right;
	}

	/**
	 * @param operator
	 *            The binary operator.
	 */
	public void setOperator(BINARY_OPERATOR operator) {
		this.operator = operator;
	}

	/**
	 * @param left
	 *            The left operand.
	 */
	public void setLeft(Expression left) {
		this.left = left;
	}

	/**
	 * @param right
	 *            The right operand.
	 */
	public void setRight(Expression right) {
		this.right = right;
	}

	@Override
	public String toString() {
		String op = "";

		switch (operator) {
		case PLUS:
			op = "+";
			break;
		case MINUS:
			op = "-";
			break;
		case TIMES:
			op = "*";
			break;
		case DIVIDE:
			op = "/";
			break;
		case LESS_THAN:
			op = "<";
			break;
		case LESS_THAN_EQUAL:
			op = "<=";
			break;
		case EQUAL:
			op = "==";
			break;
		case NOT_EQUAL:
			op = "!=";
			break;
		case AND:
			op = "&&";
			break;
		case OR:
			op = "||";
			break;
		case MODULO:
			op = "%";
			break;
		}
		return left + op + right;
	}

}
