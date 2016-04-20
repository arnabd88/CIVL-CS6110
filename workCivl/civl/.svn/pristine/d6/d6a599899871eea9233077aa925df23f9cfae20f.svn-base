/**
 * 
 */
package edu.udel.cis.vsl.civl.model.common.expression;

import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.ConditionalExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.VariableExpression;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLHeapType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

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
		this.condition.calculateDerefs();
		this.trueBranch.calculateDerefs();
		this.falseBranch.calculateDerefs();
		this.hasDerefs = this.condition.hasDerefs()
				|| this.trueBranch.hasDerefs() || this.falseBranch.hasDerefs();

	}

	@Override
	public void purelyLocalAnalysisOfVariables(Scope funcScope) {
		this.condition.purelyLocalAnalysisOfVariables(funcScope);
		this.trueBranch.purelyLocalAnalysisOfVariables(funcScope);
		this.falseBranch.purelyLocalAnalysisOfVariables(funcScope);
	}

	@Override
	public void purelyLocalAnalysis() {
		if (this.hasDerefs) {
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

	@Override
	public void replaceWith(ConditionalExpression oldExpression,
			VariableExpression newExpression) {
		if (condition == oldExpression) {
			condition = newExpression;
			return;
		}
		if (trueBranch == oldExpression) {
			trueBranch = newExpression;
			return;
		}
		if (falseBranch == oldExpression) {
			falseBranch = newExpression;
			return;
		}
		condition.replaceWith(oldExpression, newExpression);
		trueBranch.replaceWith(oldExpression, newExpression);
		falseBranch.replaceWith(oldExpression, newExpression);
	}

	@Override
	public Expression replaceWith(ConditionalExpression oldExpression,
			Expression newExpression) {
		Expression newCondition, newTrue, newFalse, result = null;

		if (this == oldExpression)
			return newExpression;

		newCondition = condition.replaceWith(oldExpression, newExpression);

		if (newCondition != null) {
			result = new CommonConditionalExpression(this.getSource(),
					newCondition, trueBranch, falseBranch);
		} else {
			newTrue = trueBranch.replaceWith(oldExpression, newExpression);

			if (newTrue != null) {
				result = new CommonConditionalExpression(this.getSource(),
						condition, newTrue, falseBranch);
			} else {
				newFalse = falseBranch
						.replaceWith(oldExpression, newExpression);

				if (newFalse != null)
					result = new CommonConditionalExpression(this.getSource(),
							condition, trueBranch, newFalse);
			}
		}

		return result;
	}

	@Override
	public Set<Variable> variableAddressedOf(Scope scope,
			CIVLHeapType heapType, CIVLType commType) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Set<Variable> variableAddressedOf(CIVLHeapType heapType,
			CIVLType commType) {
		// TODO Auto-generated method stub
		return null;
	}

}
