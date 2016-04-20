/**
 * 
 */
package edu.udel.cis.vsl.civl.model.common.expression;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Scope;
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

	@Override
	public void calculateDerefs() {
		// TODO Auto-generated method stub
		this.condition.calculateDerefs();
		this.trueBranch.calculateDerefs();
		this.falseBranch.calculateDerefs();
		this.hasDerefs = this.condition.hasDerefs() || this.trueBranch.hasDerefs() 
				|| this.falseBranch.hasDerefs();
		
	}

	@Override
	public void purelyLocalAnalysisOfVariables(Scope funcScope) {
		this.condition.purelyLocalAnalysisOfVariables(funcScope);
		this.trueBranch.purelyLocalAnalysisOfVariables(funcScope);
		this.falseBranch.purelyLocalAnalysisOfVariables(funcScope);
	}

	@Override
	public void purelyLocalAnalysis() {
		if(this.hasDerefs){
			this.purelyLocal = false;
			return;
		}
		
		this.condition.purelyLocalAnalysis();
		this.trueBranch.purelyLocalAnalysis();
		this.falseBranch.purelyLocalAnalysis();
		this.purelyLocal = this.condition.isPurelyLocal() 
				&& this.trueBranch.isPurelyLocal()
				&& this.falseBranch.isPurelyLocal();
	}

}
