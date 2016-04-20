/**
 * 
 */
package edu.udel.cis.vsl.civl.model.common.expression;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Identifier;
import edu.udel.cis.vsl.civl.model.IF.expression.ConditionalExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.QuantifiedExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.VariableExpression;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;

/**
 * @author zirkel
 * 
 */
public class CommonQuantifiedExpression extends CommonExpression implements
		QuantifiedExpression {

	private Quantifier quantifier;
	private Identifier boundVariableName;
	private CIVLType boundVariableType;
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
	public CommonQuantifiedExpression(CIVLSource source, Quantifier quantifier,
			Identifier boundVariableName, CIVLType boundVariableType,
			Expression restriction, Expression expression) {
		super(source);
		this.quantifier = quantifier;
		this.boundVariableName = boundVariableName;
		this.boundVariableType = boundVariableType;
		this.restriction = restriction;
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
		result += " {" + boundVariableName + " " + boundVariableType + " | "
				+ restriction + "} " + expression;
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
					quantifier, boundVariableName, boundVariableType,
					newRestriction, expression);
		} else {
			Expression newExpressionField = expression.replaceWith(
					oldExpression, newExpression);

			if (newExpressionField != null)
				result = new CommonQuantifiedExpression(this.getSource(),
						quantifier, boundVariableName, boundVariableType,
						restriction, newExpressionField);
		}

		if (result != null)
			result.setExpressionType(expressionType);

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
}
