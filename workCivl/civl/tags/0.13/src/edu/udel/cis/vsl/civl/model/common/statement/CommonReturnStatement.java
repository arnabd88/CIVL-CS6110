/**
 * 
 */
package edu.udel.cis.vsl.civl.model.common.statement;

import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.CIVLFunction;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.ConditionalExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.VariableExpression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.ReturnStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

/**
 * A return statement.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public class CommonReturnStatement extends CommonStatement implements
		ReturnStatement {

	private Expression expression;

	private CIVLFunction function;

	/**
	 * A return statement.
	 * 
	 * @param source
	 *            The source location for this return statement.
	 * @param expression
	 *            The expression being returned. Null if non-existent.
	 */
	public CommonReturnStatement(CIVLSource civlSource, Location source,
			Expression expression, CIVLFunction function) {
		super(civlSource, source);
		this.expression = expression;
		this.function = function;
	}

	/**
	 * @return The expression being returned. Null if non-existent.
	 */
	@Override
	public Expression expression() {
		return expression;
	}

	/**
	 * @param expression
	 *            The expression being returned. Null if non-existent.
	 */
	@Override
	public void setExpression(Expression expression) {
		this.expression = expression;
	}

	@Override
	public String toString() {
		if (expression == null) {
			return "return (" + this.function.name().name() + ")";
		}
		return "return " + expression + " (" + this.function.name().name()
				+ ")";
	}

	@Override
	public void calculateDerefs() {
		if (this.expression != null) {
			this.expression.calculateDerefs();
			this.hasDerefs = this.expression.hasDerefs();
		} else
			this.hasDerefs = false;

	}

	@Override
	public void purelyLocalAnalysisOfVariables(Scope funcScope) {
		super.purelyLocalAnalysisOfVariables(funcScope);
		if (this.expression != null)
			this.expression.purelyLocalAnalysisOfVariables(funcScope);
	}

	@Override
	public void purelyLocalAnalysis() {
		this.guard().purelyLocalAnalysis();
		if (this.expression != null) {
			this.expression.purelyLocalAnalysis();
			this.purelyLocal = this.expression.isPurelyLocal()
					&& this.guard().isPurelyLocal();
		} else
			this.purelyLocal = this.guard().isPurelyLocal();
	}

	@Override
	public void replaceWith(ConditionalExpression oldExpression,
			VariableExpression newExpression) {
		super.replaceWith(oldExpression, newExpression);

		if (expression != null) {
			if (expression == oldExpression) {
				expression = newExpression;
				return;
			}
			expression.replaceWith(oldExpression, newExpression);
		}
	}

	@Override
	public Statement replaceWith(ConditionalExpression oldExpression,
			Expression newExpression) {
		Expression newGuard = guardReplaceWith(oldExpression, newExpression);
		CommonReturnStatement newStatement = null;

		if (newGuard != null) {
			newStatement = new CommonReturnStatement(this.getSource(),
					this.source(), this.expression, this.function);
			newStatement.setGuard(newGuard);
		} else if (expression != null) {
			Expression newExpressionField = expression.replaceWith(
					oldExpression, newExpression);

			if (newExpressionField != null) {
				newStatement = new CommonReturnStatement(this.getSource(),
						this.source(), newExpressionField, this.function);
				newStatement.setGuard(this.guard());
			}
		}
		return newStatement;
	}

	@Override
	public Set<Variable> variableAddressedOf(Scope scope) {
		if (expression != null)
			return expression.variableAddressedOf(scope);
		return null;
	}

	@Override
	public Set<Variable> variableAddressedOf() {
		if (expression != null)
			return expression.variableAddressedOf();
		return null;
	}

	@Override
	public StatementKind statementKind() {
		return StatementKind.RETURN;
	}

}
