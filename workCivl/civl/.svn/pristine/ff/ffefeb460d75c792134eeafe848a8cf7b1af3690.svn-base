/**
 * 
 */
package edu.udel.cis.vsl.civl.model.common.expression;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.expression.ConditionalExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;

/**
 * @author zirkel
 * 
 */
public class CommonConditionalExpression extends CommonExpression implements
		ConditionalExpression {

	Expression condition;
	Expression trueBranch;
	Expression falseBranch;

	/**
	 * The ternary conditional expression ("?" in C).
	 * 
	 * @param condition
	 *            The condition evaluated in this conditional.
	 * @param trueBranch
	 *            The expression returned if the branch evaluates to true.
	 * @param falseBranch
	 *            The expression returned if the branch evaluates to false.
	 */
	public CommonConditionalExpression(CIVLSource source, Expression condition,
			Expression trueBranch, Expression falseBranch) {
		super(source);
		this.condition = condition;
		this.trueBranch = trueBranch;
		this.falseBranch = falseBranch;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * edu.udel.cis.vsl.civl.model.IF.expression.ConditionalExpression#getCondition
	 * ()
	 */
	@Override
	public Expression getCondition() {
		return condition;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * edu.udel.cis.vsl.civl.model.IF.expression.ConditionalExpression#getTrueBranch
	 * ()
	 */
	@Override
	public Expression getTrueBranch() {
		return trueBranch;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see edu.udel.cis.vsl.civl.model.IF.expression.ConditionalExpression#
	 * getFalseBranch()
	 */
	@Override
	public Expression getFalseBranch() {
		return falseBranch;
	}

	@Override
	public String toString() {
		return "(" + condition + " ? " + trueBranch + " : " + falseBranch + ")";
	}

	@Override
	public ExpressionKind expressionKind() {
		return ExpressionKind.COND;
	}

}
