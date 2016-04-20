/**
 * 
 */
package edu.udel.cis.vsl.civl.model.common.expression;

import java.util.HashSet;
import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Identifier;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.ConditionalExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.QuantifiedExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.VariableExpression;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

/**
 * @author zirkel
 * 
 */
public class CommonQuantifiedExpression extends CommonExpression implements
		QuantifiedExpression {

	private Quantifier quantifier;
	private Identifier boundVariableName;
	private CIVLType boundVariableType;
	private boolean isRange;
	private Expression lower;
	private Expression upper;
	private Expression restriction;
	private Expression expression;

	/**
	 * @param source
	 *            The source file information for this expression.
	 * @param quantifier
	 *            The type of quantifier.
	 * @param boundVariableName
	 *            The name of the bound variable.
	 * @param boundVariableType
	 *            The type of the bound variable.
	 * @param restriction
	 *            The restriction on the quantified variable.
	 * @param expression
	 *            The quantified expression.
	 */
	public CommonQuantifiedExpression(CIVLSource source, Scope scope,
			CIVLType type, Quantifier quantifier, Identifier boundVariableName,
			CIVLType boundVariableType, Expression restriction,
			Expression expression) {
		super(source, scope, scope, type);
		this.quantifier = quantifier;
		this.boundVariableName = boundVariableName;
		this.boundVariableType = boundVariableType;
		isRange = false;
		this.lower = this.upper = null;
		this.restriction = restriction;
		this.expression = expression;
	}

	/**
	 * @param source
	 *            The source file information for this expression.
	 * @param quantifier
	 *            The type of quantifier.
	 * @param boundVariableName
	 *            The name of the bound variable.
	 * @param boundVariableType
	 *            The type of the bound variable.
	 * @param lower
	 *            The lower bound on the range of this bound variable.
	 * @param upper
	 *            The upper bound on the range of this bound variable.
	 * @param expression
	 *            The quantified expression.
	 */
	public CommonQuantifiedExpression(CIVLSource source, Scope scope,
			CIVLType type, Quantifier quantifier, Identifier boundVariableName,
			CIVLType boundVariableType, Expression lower, Expression upper,
			Expression expression) {
		super(source, scope, scope, type);
		this.quantifier = quantifier;
		this.boundVariableName = boundVariableName;
		this.boundVariableType = boundVariableType;
		isRange = true;
		this.lower = lower;
		this.upper = upper;
		this.restriction = null;
		this.expression = expression;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * edu.udel.cis.vsl.civl.model.IF.expression.Expression#expressionKind()
	 */
	@Override
	public ExpressionKind expressionKind() {
		return ExpressionKind.QUANTIFIER;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * edu.udel.cis.vsl.civl.model.IF.expression.QuantifiedExpression#quantifier
	 * ()
	 */
	@Override
	public Quantifier quantifier() {
		return quantifier;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see edu.udel.cis.vsl.civl.model.IF.expression.QuantifiedExpression#
	 * boundRestriction()
	 */
	@Override
	public Expression boundRestriction() {
		return restriction;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * edu.udel.cis.vsl.civl.model.IF.expression.QuantifiedExpression#expression
	 * ()
	 */
	@Override
	public Expression expression() {
		return expression;
	}

	@Override
	public String toString() {
		String result = "";

		switch (quantifier) {
		case EXISTS:
			result += "EXISTS";
			break;
		case FORALL:
			result += "FORALL";
			break;
		case UNIFORM:
			result += "UNIFORM";
			break;
		default:
			result += "UNKNOWN_QUANTIFIER";
			break;
		}
		result += " {" + boundVariableType + " " + boundVariableName;

		if (isRange) {
			result += "=" + lower + ".." + upper;
		} else {
			result += " | " + restriction;
		}
		result += "} " + expression;
		return result;
	}

	@Override
	public void replaceWith(ConditionalExpression oldExpression,
			VariableExpression newExpression) {
		if (restriction == oldExpression) {
			restriction = newExpression;
			return;
		}
		if (expression == oldExpression) {
			expression = newExpression;
			return;
		}
		restriction.replaceWith(oldExpression, newExpression);
		expression.replaceWith(oldExpression, newExpression);
	}

	@Override
	public Expression replaceWith(ConditionalExpression oldExpression,
			Expression newExpression) {
		Expression newRestriction = restriction.replaceWith(oldExpression,
				newExpression);
		CommonQuantifiedExpression result = null;

		if (newRestriction != null) {
			result = new CommonQuantifiedExpression(this.getSource(),
					this.expressionScope(), this.expressionType, quantifier,
					boundVariableName, boundVariableType, newRestriction,
					expression);
		} else {
			Expression newExpressionField = expression.replaceWith(
					oldExpression, newExpression);

			if (newExpressionField != null)
				result = new CommonQuantifiedExpression(this.getSource(),
						this.expressionScope(), this.expressionType,
						quantifier, boundVariableName, boundVariableType,
						restriction, newExpressionField);
		}
		return result;
	}

	@Override
	public Identifier boundVariableName() {
		return boundVariableName;
	}

	@Override
	public CIVLType boundVariableType() {
		return boundVariableType;
	}

	@Override
	public boolean isRange() {
		return isRange;
	}

	@Override
	public Expression lower() {
		return lower;
	}

	@Override
	public Expression upper() {
		return upper;
	}

	@Override
	public Set<Variable> variableAddressedOf(Scope scope) {
		Set<Variable> variableSet = new HashSet<>();
		Set<Variable> operandResult;

		if (expression != null) {
			operandResult = expression.variableAddressedOf(scope);
			if (operandResult != null)
				variableSet.addAll(operandResult);
		}
		if (lower != null) {
			operandResult = lower.variableAddressedOf(scope);
			if (operandResult != null)
				variableSet.addAll(operandResult);
		}
		if (upper != null) {
			operandResult = upper.variableAddressedOf(scope);
			if (operandResult != null)
				variableSet.addAll(operandResult);
		}
		return variableSet;
	}

	@Override
	public Set<Variable> variableAddressedOf() {
		Set<Variable> variableSet = new HashSet<>();
		Set<Variable> operandResult;

		if (expression != null) {
			operandResult = expression.variableAddressedOf();
			if (operandResult != null)
				variableSet.addAll(operandResult);
		}
		if (lower != null) {
			operandResult = lower.variableAddressedOf();
			if (operandResult != null)
				variableSet.addAll(operandResult);
		}
		if (upper != null) {
			operandResult = upper.variableAddressedOf();
			if (operandResult != null)
				variableSet.addAll(operandResult);
		}
		return variableSet;
	}

	@Override
	protected boolean expressionEquals(Expression expression) {
		QuantifiedExpression that = (QuantifiedExpression) expression;

		return this.quantifier.equals(that.quantifier())
				&& this.isRange == that.isRange()
				&& this.expression.equals(that.expression())
				&& (this.isRange ? this.lower.equals(that.lower())
						&& this.upper.equals(that.upper()) : this.restriction
						.equals(that.boundRestriction()));
	}
}
