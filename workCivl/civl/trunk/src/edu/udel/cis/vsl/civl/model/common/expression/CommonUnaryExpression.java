/**
 * 
 */
package edu.udel.cis.vsl.civl.model.common.expression;

import java.util.HashSet;
import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.CIVLInternalException;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.ConditionalExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.UnaryExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.VariableExpression;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;

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
	public CommonUnaryExpression(CIVLSource source, CIVLType type,
			UNARY_OPERATOR operator, Expression operand) {
		super(source, operand.expressionScope(), operand.lowestScope(), type);
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
		return this.operatorToString() + "(" + operand + ")";
	}

	@Override
	public ExpressionKind expressionKind() {
		return ExpressionKind.UNARY;
	}

	@Override
	public void calculateDerefs() {
		this.operand.calculateDerefs();
		this.hasDerefs = this.operand.hasDerefs();
	}

	@Override
	public void purelyLocalAnalysisOfVariables(Scope funcScope) {
		this.operand.purelyLocalAnalysisOfVariables(funcScope);
	}

	@Override
	public void purelyLocalAnalysis() {
		if (this.hasDerefs) {
			this.purelyLocal = false;
			return;
		}

		this.operand.purelyLocalAnalysis();
		this.purelyLocal = this.operand.isPurelyLocal();
	}

	@Override
	public void replaceWith(ConditionalExpression oldExpression,
			VariableExpression newExpression) {
		if (operand == oldExpression) {
			operand = newExpression;
			return;
		}
		operand.replaceWith(oldExpression, newExpression);
	}

	@Override
	public Expression replaceWith(ConditionalExpression oldExpression,
			Expression newExpression) {
		Expression newOperand = operand.replaceWith(oldExpression,
				newExpression);
		CommonUnaryExpression result = null;

		if (newOperand != null)
			result = new CommonUnaryExpression(this.getSource(),
					this.expressionType, operator, newOperand);

		return result;
	}

	@Override
	public Set<Variable> variableAddressedOf(Scope scope) {
		Set<Variable> variableSet = new HashSet<>();
		Set<Variable> operandResult = operand.variableAddressedOf(scope);

		if (operandResult != null)
			variableSet.addAll(operandResult);
		return variableSet;
	}

	@Override
	public Set<Variable> variableAddressedOf() {
		Set<Variable> variableSet = new HashSet<>();
		Set<Variable> operandResult = operand.variableAddressedOf();

		if (operandResult != null)
			variableSet.addAll(operandResult);
		return variableSet;
	}

	@Override
	public void calculateConstantValueWork(SymbolicUniverse universe) {
		SymbolicExpression operandValue;

		operand.calculateConstantValue(universe);
		operandValue = this.operand.constantValue();
		if (operandValue == null)
			return;
		switch (operator) {
		case NEGATIVE:
			this.constantValue = universe
					.minus((NumericExpression) operandValue);
			break;
		case NOT:
			this.constantValue = universe.not((BooleanExpression) operandValue);
			break;
		case BIG_O:
		case VALID:
			break;
		default:
			throw new CIVLInternalException("Unknown unary operator: "
					+ operator, this);
		}
	}

	@Override
	protected boolean expressionEquals(Expression expression) {
		UnaryExpression that = (UnaryExpression) expression;

		return this.operator == that.operator()
				&& this.operand.equals(that.operand());
	}

	@Override
	public String operatorToString() {
		String op = "";

		switch (operator) {
		case NEGATIVE:
			op = "-";
			break;
		case NOT:
			op = "!";
			break;
		case BIG_O:
			op = "$O";
			break;
		case VALID:
			op = "\\valid";
			break;
		default:
			throw new CIVLInternalException("Unknown unary operator: "
					+ operator, this);
		}
		return op;
	}

	@Override
	public boolean containsHere() {
		return operand.containsHere();
	}
}
