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
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;

/**
 * A binary operation.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public class CommonBinaryExpression extends CommonExpression implements
		BinaryExpression {

	/* ************************** Private Fields *************************** */

	/**
	 * The operator of this binary expression.
	 * 
	 * @see BINARY_OPERATOR
	 */
	private BINARY_OPERATOR operator;

	/**
	 * The left-hand-side operand.
	 */
	private Expression left;

	/**
	 * The right-hand-side operand.
	 */
	private Expression right;

	/* **************************** Constructor **************************** */

	/**
	 * Create a new instance of a binary expression.
	 * 
	 * @param source
	 *            The source information corresponding to this expression.
	 * @param scope
	 *            The highest scope that this expression accessed through its
	 *            operands.
	 * @param type
	 *            The type of this expression.
	 * @param operator
	 *            The operator of this expression.
	 * @param left
	 *            The left-hand-side operand.
	 * @param right
	 *            The right-hand-side operand.
	 */
	public CommonBinaryExpression(CIVLSource source, Scope hscope,
			Scope lscope, CIVLType type, BINARY_OPERATOR operator,
			Expression left, Expression right) {
		super(source, hscope, lscope, type);
		this.operator = operator;
		this.left = left;
		this.right = right;
	}

	/* ******************* Methods from BinaryExpression ******************* */

	/**
	 * @return The binary operator
	 */
	@Override
	public BINARY_OPERATOR operator() {
		return operator;
	}

	/**
	 * @return The left operand.
	 */
	@Override
	public Expression left() {
		return left;
	}

	/**
	 * @return The right operand.
	 */
	@Override
	public Expression right() {
		return right;
	}

	/* ********************** Methods from Expression ********************** */

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
					expressionScope(), lowestScope(), expressionType,
					this.operator, newLeft, right);
		} else {
			Expression newRight = right.replaceWith(oldExpression,
					newExpression);

			if (newRight != null)
				result = new CommonBinaryExpression(this.getSource(),
						expressionScope(), lowestScope(), expressionType,
						this.operator, left, newRight);
		}
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

	/* ********************** Methods from Expression ********************** */

	@Override
	public String toString() {
		String op = this.operatorToString();

		return "(" + left + op + right + ")";
	}

	@Override
	public void calculateConstantValue(SymbolicUniverse universe) {
		SymbolicExpression leftValue = left.constantValue(), rightValue = right
				.constantValue();

		if (leftValue == null || rightValue == null)
			return;
		switch (operator) {
		case BITAND:
		case BITOR:
		case BITXOR:
			break;
		case PLUS:
			constantValue = universe.add((NumericExpression) leftValue,
					(NumericExpression) rightValue);
			break;
		case MINUS:
			constantValue = universe.subtract((NumericExpression) leftValue,
					(NumericExpression) rightValue);
			break;
		case TIMES:
			constantValue = universe.multiply((NumericExpression) leftValue,
					(NumericExpression) rightValue);
			break;
		case DIVIDE:
			constantValue = universe.divide((NumericExpression) leftValue,
					(NumericExpression) rightValue);
			break;
		case LESS_THAN:
			constantValue = universe.lessThan((NumericExpression) leftValue,
					(NumericExpression) rightValue);
			break;
		case LESS_THAN_EQUAL:
			constantValue = universe.lessThanEquals(
					(NumericExpression) leftValue,
					(NumericExpression) rightValue);
			break;
		case EQUAL:
			constantValue = universe.equals((NumericExpression) leftValue,
					(NumericExpression) rightValue);
			break;
		case NOT_EQUAL:
			constantValue = universe.not(universe.equals(
					(NumericExpression) leftValue,
					(NumericExpression) rightValue));
			break;
		case AND:
			constantValue = universe.and((BooleanExpression) leftValue,
					(BooleanExpression) rightValue);
			break;
		case OR:
			constantValue = universe.or((BooleanExpression) leftValue,
					(BooleanExpression) rightValue);
			break;
		case IMPLIES:
			constantValue = universe.implies((BooleanExpression) leftValue,
					(BooleanExpression) rightValue);
			break;
		case MODULO:
			constantValue = universe.modulo((NumericExpression) leftValue,
					(NumericExpression) rightValue);
			break;
		case POINTER_ADD:
		case POINTER_SUBTRACT:
		case SHIFTLEFT:
		case SHIFTRIGHT:
			break;
		default:
			throw new CIVLInternalException("Unknown operator: " + operator,
					this);
		}
	}

	@Override
	protected boolean expressionEquals(Expression expression) {
		BinaryExpression that = (BinaryExpression) expression;

		return this.left.equals(that.left()) && this.right.equals(that.right());
	}

	@Override
	public String operatorToString() {
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
		return op;
	}
}
