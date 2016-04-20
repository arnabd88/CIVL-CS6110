/**
 * 
 */
package edu.udel.cis.vsl.civl.model.common.statement;

import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.ConditionalExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.VariableExpression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.AssumeStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

/**
 * An assume statement provides an expression which is to be added to the path
 * condition.
 * 
 * @author zirkel
 * 
 */
public class CommonAssumeStatement extends CommonStatement implements
		AssumeStatement {

	private Expression expression;

	/**
	 * An assume statement.
	 * 
	 * @param source
	 *            The source location for this statement.
	 * @param expression
	 *            The expression being added to the path condition.
	 */
	public CommonAssumeStatement(CIVLSource civlSource, Location source,
			Expression expression) {
		super(civlSource, source);
		this.expression = expression;
	}

	/**
	 * @return The expression being added to the path condition.
	 */
	@Override
	public Expression getExpression() {
		return expression;
	}

	/**
	 * @param expression
	 *            The expression being added to the path condition.
	 */
	@Override
	public void setExpression(Expression expression) {
		this.expression = expression;
	}

	@Override
	public String toString() {
		return "$assume " + expression;
	}

	@Override
	public void calculateDerefs() {
		// this.expression.calculateDerefs();
		// this.hasDerefs = this.expression.hasDerefs();
	}

	@Override
	public void purelyLocalAnalysisOfVariables(Scope funcScope) {
		super.purelyLocalAnalysisOfVariables(funcScope);
		this.expression.purelyLocalAnalysisOfVariables(funcScope);
	}

	@Override
	public void purelyLocalAnalysis() {
		// TODO check
		this.expression.purelyLocalAnalysis();
		this.purelyLocal = this.expression.isPurelyLocal();
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
		CommonAssumeStatement newStatement = null;

		if (newGuard != null) {
			newStatement = new CommonAssumeStatement(this.getSource(),
					this.source(), this.expression);
			newStatement.setGuard(newGuard);
		} else {
			Expression newExpressionField = expression.replaceWith(
					oldExpression, newExpression);

			if (newExpressionField != null) {
				newStatement = new CommonAssumeStatement(this.getSource(),
						this.source(), newExpressionField);
				newStatement.setGuard(this.guard());
			}
		}
		return newStatement;
	}

	@Override
	public Set<Variable> variableAddressedOf(Scope scope) {
		return expression.variableAddressedOf(scope);
	}

	@Override
	public Set<Variable> variableAddressedOf() {
		return expression.variableAddressedOf();
	}

	@Override
	public StatementKind statementKind() {
		return StatementKind.ASSUME;
	}
}
