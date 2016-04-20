/**
 * 
 */
package edu.udel.cis.vsl.civl.model.common.statement;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.ConditionalExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.VariableExpression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.AssertStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;

/**
 * An assert statement.
 * 
 * @author zirkel
 * 
 */
public class CommonAssertStatement extends CommonStatement implements
		AssertStatement {

	private boolean isCollective = false;
	private Expression expression;

	/**
	 * @param source
	 *            The source location for this statement.
	 * @param expression
	 *            The expression being checked.
	 */
	public CommonAssertStatement(CIVLSource civlSource, Location source,
			Expression expression) {
		super(civlSource, source);
		this.expression = expression;
	}

	/**
	 * @return Whether this is a collective assertion.
	 */
	@Override
	public boolean isCollective() {
		return isCollective;
	}

	/**
	 * @return The expression being checked.
	 */
	@Override
	public Expression getExpression() {
		return expression;
	}

	/**
	 * @param isCollective
	 *            Whether this is a collective assertion.
	 */
	@Override
	public void setCollective(boolean isCollective) {
		this.isCollective = isCollective;
	}

	/**
	 * @param expression
	 *            The expression being checked.
	 */
	@Override
	public void setExpression(Expression expression) {
		this.expression = expression;
	}

	@Override
	public String toString() {
		return "$assert " + expression;
	}

	@Override
	public void calculateDerefs() {
		this.expression.calculateDerefs();
		this.hasDerefs = this.expression.hasDerefs();
	}

	@Override
	public void purelyLocalAnalysisOfVariables(Scope funcScope) {
		super.purelyLocalAnalysisOfVariables(funcScope);
		this.expression.purelyLocalAnalysisOfVariables(funcScope);
	}

	@Override
	public void purelyLocalAnalysis() {
		this.guard().purelyLocalAnalysis();
		this.expression.purelyLocalAnalysis();
		this.purelyLocal = this.guard().isPurelyLocal()
				&& this.expression.isPurelyLocal();
	}

	@Override
	public void replaceWith(ConditionalExpression oldExpression,
			VariableExpression newExpression) {
		super.replaceWith(oldExpression, newExpression);

		if (expression == oldExpression) {
			expression = newExpression;
			return;
		}

		this.expression.replaceWith(oldExpression, newExpression);
	}

	@Override
	public Statement replaceWith(ConditionalExpression oldExpression,
			Expression newExpression) {
		Expression newGuard = guardReplaceWith(oldExpression, newExpression);
		CommonAssertStatement newStatement = null;

		if (newGuard != null) {
			newStatement = new CommonAssertStatement(this.getSource(),
					this.source(), this.expression);
			newStatement.setGuard(newGuard);
		} else {
			Expression newExpressionField = expression.replaceWith(
					oldExpression, newExpression);

			if (newExpressionField != null) {
				newStatement = new CommonAssertStatement(this.getSource(),
						this.source(), newExpressionField);
				newStatement.setGuard(this.guard());
			}
		}
		return newStatement;
	}

}
