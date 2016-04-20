/**
 * 
 */
package edu.udel.cis.vsl.civl.model.common.expression;

import java.util.HashSet;
import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.CIVLInternalException;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.BinaryExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.ConditionalExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.VariableExpression;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

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
	 * @param source
	 *            The CIVL source
	 * @param operator
	 *            The binary operator.
	 * @param left
	 *            The left operand.
	 * @param right
	 *            The right operand.
	 */
	public CommonBinaryExpression(CIVLSource source, BINARY_OPERATOR operator,
			Expression left, Expression right) {
		super(source);
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
		case BITAND:
			op = "&";
			break;
		case BITOR:
			op = "|";
			break;
		case BITXOR:
			op = "^";
			break;
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
		case IMPLIES:
			op = "=>";
			break;
		case MODULO:
			op = "%";
			break;
		case POINTER_ADD:
			op = "+";
			break;
		case POINTER_SUBTRACT:
			op = "-";
			break;
		case SHIFTLEFT:
			op = "<<";
			break;
		case SHIFTRIGHT:
			op = ">>";
			break;
		default:
			throw new CIVLInternalException("Unknown operator: " + operator,
					this);
		}
		return "(" + left + op + right + ")";
	}

	@Override
	public ExpressionKind expressionKind() {
		return ExpressionKind.BINARY;
	}

	@Override
	public void calculateDerefs() {
		this.left.calculateDerefs();
		this.right.calculateDerefs();
		this.hasDerefs = this.left.hasDerefs() || this.right.hasDerefs();
	}

	@Override
	public void purelyLocalAnalysisOfVariables(Scope funcScope) {
		this.left.purelyLocalAnalysisOfVariables(funcScope);
		this.right.purelyLocalAnalysisOfVariables(funcScope);
	}

	@Override
	public void purelyLocalAnalysis() {
		if (this.hasDerefs) {
			this.purelyLocal = false;
			return;
		}
		this.left.purelyLocalAnalysis();
		this.right.purelyLocalAnalysis();
		this.purelyLocal = this.left.isPurelyLocal()
				&& this.right.isPurelyLocal();
	}

	@Override
	public void replaceWith(ConditionalExpression oldExpression,
			VariableExpression newExpression) {
		if (left == oldExpression) {
			left = newExpression;
			return;
		}

		if (right == oldExpression) {
			right = newExpression;
			return;
		}

		left.replaceWith(oldExpression, newExpression);
		right.replaceWith(oldExpression, newExpression);
	}

	@Override
	public Expression replaceWith(ConditionalExpression oldExpression,
			Expression newExpression) {
		Expression newLeft = left.replaceWith(oldExpression, newExpression);
		CommonBinaryExpression result = null;

		if (newLeft != null) {
			result = new CommonBinaryExpression(this.getSource(),
					this.operator, newLeft, right);
		} else {
			Expression newRight = right.replaceWith(oldExpression,
					newExpression);

			if (newRight != null)
				result = new CommonBinaryExpression(this.getSource(),
						this.operator, left, newRight);
		}

		if (result != null)
			result.setExpressionType(expressionType);

		return result;
	}

	@Override
	public Set<Variable> variableAddressedOf(Scope scope) {
		Set<Variable> variableSet = new HashSet<>();
		Set<Variable> operandResult = left.variableAddressedOf(scope);

		if (operandResult != null)
			variableSet.addAll(operandResult);
		operandResult = right.variableAddressedOf(scope);
		if (operandResult != null)
			variableSet.addAll(operandResult);
		return variableSet;
	}

	@Override
	public Set<Variable> variableAddressedOf() {
		Set<Variable> variableSet = new HashSet<>();
		Set<Variable> operandResult = left.variableAddressedOf();

		if (operandResult != null)
			variableSet.addAll(operandResult);
		operandResult = right.variableAddressedOf();
		if (operandResult != null)
			variableSet.addAll(operandResult);
		return variableSet;
	}
}
