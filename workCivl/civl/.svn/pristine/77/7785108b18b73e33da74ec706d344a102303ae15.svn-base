/**
 * 
 */
package edu.udel.cis.vsl.civl.model.common.expression;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.QuantifiedExpression;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

/**
 * @author zirkel
 * 
 */
public class CommonQuantifiedExpression extends CommonExpression implements
		QuantifiedExpression {

	private Quantifier quantifier;
	private Variable variable;
	private Expression restriction;
	private Expression expression;

	/**
	 * @param source
	 *            The source file information for this expression.
	 * @param quantifier
	 *            The type of quantifier.
	 * @param restriction
	 *            The restriction on the quantified variable.
	 * @param expression
	 *            The quantified expression.
	 */
	public CommonQuantifiedExpression(CIVLSource source, Quantifier quantifier,
			Variable variable, Expression restriction, Expression expression) {
		super(source);
		this.quantifier = quantifier;
		this.variable = variable;
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
	 * @see
	 * edu.udel.cis.vsl.civl.model.IF.expression.QuantifiedExpression#boundVariable
	 * ()
	 */
	@Override
	public Variable boundVariable() {
		return variable;
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
		result += " {" + variable + " | " + restriction + "} " + expression;
		return result;
	}

}
