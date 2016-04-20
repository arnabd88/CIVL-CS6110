/**
 * 
 */
package edu.udel.cis.vsl.civl.model.common.expression;

import java.util.HashSet;
import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.CastExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.ConditionalExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.VariableExpression;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

/**
 * A cast of an expression to a different type.
 * 
 * @author zirkel
 * 
 */
public class CommonCastExpression extends CommonExpression implements
		CastExpression {

	private CIVLType type;
	private Expression expression;

	/**
	 * A cast of an expression to a different type.
	 * 
	 * @param type
	 *            The type to which the expression is cast.
	 * @param expression
	 *            The expression being cast to a new type.
	 */
	public CommonCastExpression(CIVLSource source, CIVLType type,
			Expression expression) {
		super(source);
		this.type = type;
		this.expression = expression;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * edu.udel.cis.vsl.civl.model.IF.expression.CastExpression#getExpression()
	 */
	@Override
	public Expression getExpression() {
		return expression;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * edu.udel.cis.vsl.civl.model.IF.expression.CastExpression#getCastType()
	 */
	@Override
	public CIVLType getCastType() {
		return type;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * edu.udel.cis.vsl.civl.model.IF.expression.CastExpression#setExpression
	 * (edu.udel.cis.vsl.civl.model.IF.expression.Expression)
	 */
	@Override
	public void setExpression(Expression expression) {
		this.expression = expression;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * edu.udel.cis.vsl.civl.model.IF.expression.CastExpression#setType(edu.
	 * udel.cis.vsl.civl.model.IF.type.Type)
	 */
	@Override
	public void setCastType(CIVLType type) {
		this.type = type;
	}

	@Override
	public String toString() {
		return "(" + type + ") " + expression;
	}

	@Override
	public ExpressionKind expressionKind() {
		return ExpressionKind.CAST;
	}

	@Override
	public void calculateDerefs() {
		this.expression.calculateDerefs();
		this.hasDerefs = this.expression.hasDerefs();
	}

	@Override
	public void purelyLocalAnalysisOfVariables(Scope funcScope) {
		this.expression.purelyLocalAnalysisOfVariables(funcScope);
	}

	@Override
	public void purelyLocalAnalysis() {
		if (this.hasDerefs) {
			this.purelyLocal = false;
			return;
		}
		this.expression.purelyLocalAnalysis();
		this.purelyLocal = this.expression.isPurelyLocal();
	}

	@Override
	public void replaceWith(ConditionalExpression oldExpression,
			VariableExpression newExpression) {
		if (expression == oldExpression) {
			expression = newExpression;
			return;
		}
		expression.replaceWith(oldExpression, newExpression);
	}

	@Override
	public Expression replaceWith(ConditionalExpression oldExpression,
			Expression newExpression) {
		Expression newOperand = expression.replaceWith(oldExpression,
				newExpression);
		CommonCastExpression result = null;

		if (newOperand != null) {
			result = new CommonCastExpression(this.getSource(), this.type,
					newOperand);
		}

		if (result != null)
			result.setExpressionType(expressionType);

		return result;

	}

	@Override
	public Set<Variable> variableAddressedOf(Scope scope) {
		Set<Variable> variableSet = new HashSet<>();
		Set<Variable> operandResult = expression.variableAddressedOf(scope);

		if (operandResult != null)
			variableSet.addAll(operandResult);
		return variableSet;
	}

	@Override
	public Set<Variable> variableAddressedOf() {
		Set<Variable> variableSet = new HashSet<>();
		Set<Variable> operandResult = expression.variableAddressedOf();

		if (operandResult != null)
			variableSet.addAll(operandResult);
		return variableSet;
	}

}
