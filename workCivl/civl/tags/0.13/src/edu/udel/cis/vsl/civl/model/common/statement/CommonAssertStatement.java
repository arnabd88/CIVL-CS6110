/**
 * 
 */
package edu.udel.cis.vsl.civl.model.common.statement;

import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.ConditionalExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.VariableExpression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.AssertStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

/**
 * An assert statement that checks if a given boolean expression is satisfied.
 * 
 * 
 * @author Manchun Zheng (zmanchun)
 * 
 */
public class CommonAssertStatement extends CommonStatement implements
		AssertStatement {

	private Expression condition;

	private Expression[] explanation;

	/**
	 * An assert statement.
	 * 
	 * @param source
	 *            The source location for this statement.
	 * @param condition
	 *            The expression being added to the path condition.
	 * @param
	 */
	public CommonAssertStatement(CIVLSource civlSource, Location source,
			Expression condition, Expression[] explanation) {
		super(civlSource, source);
		this.condition = condition;
		this.explanation = explanation;
	}

	/**
	 * @return The expression being added to the path condition.
	 */
	@Override
	public Expression getCondition() {
		return condition;
	}

	/**
	 * @param condition
	 *            The expression being added to the path condition.
	 */
	@Override
	public void setCondition(Expression condition) {
		this.condition = condition;
	}

	@Override
	public String toString() {
		StringBuffer result = new StringBuffer();

		result.append("$assert ");
		result.append(condition);
		if (this.explanation != null) {
			int numArgs = this.explanation.length;

			result.append(": ");
			for (int i = 0; i < numArgs; i++) {
				if (i != 0)
					result.append(", ");
				result.append(this.explanation[i]);
			}
		}
		return "$assert " + condition;
	}

	@Override
	public void calculateDerefs() {
		this.condition.calculateDerefs();
		this.hasDerefs = this.condition.hasDerefs();
		if (!hasDerefs && this.explanation != null) {
			for (Expression arg : explanation) {
				arg.calculateDerefs();
				this.hasDerefs = arg.hasDerefs();
				if (this.hasDerefs)
					return;
			}
		}
	}

	@Override
	public void purelyLocalAnalysisOfVariables(Scope funcScope) {
		super.purelyLocalAnalysisOfVariables(funcScope);
		this.condition.purelyLocalAnalysisOfVariables(funcScope);
	}

	@Override
	public void purelyLocalAnalysis() {
		this.condition.purelyLocalAnalysis();
		if (!this.condition.isPurelyLocal()) {
			this.purelyLocal = false;
			return;
		}
		if (this.purelyLocal && this.explanation != null) {
			for (Expression arg : explanation) {
				arg.purelyLocalAnalysis();
				if (!arg.isPurelyLocal()) {
					this.purelyLocal = false;
					return;
				}
			}
		}
		this.purelyLocal = true;
	}

	@Override
	public void replaceWith(ConditionalExpression oldExpression,
			VariableExpression newExpression) {
		super.replaceWith(oldExpression, newExpression);

		if (condition == oldExpression) {
			condition = newExpression;
			return;
		}
		this.condition.replaceWith(oldExpression, newExpression);
		if (this.explanation != null) {
			int numArgs = this.explanation.length;
			for (int i = 0; i < numArgs; i++) {
				if (this.explanation[i] == oldExpression) {
					this.explanation[i] = newExpression;
					return;
				}
				this.explanation[i].replaceWith(oldExpression, newExpression);
			}
		}
	}

	@Override
	public Statement replaceWith(ConditionalExpression oldExpression,
			Expression newExpression) {
		Expression newGuard = guardReplaceWith(oldExpression, newExpression);
		CommonAssertStatement newStatement = null;

		if (newGuard != null) {
			newStatement = new CommonAssertStatement(this.getSource(),
					this.source(), this.condition, this.explanation);
			newStatement.setGuard(newGuard);
		} else {
			Expression newExpressionField = condition.replaceWith(
					oldExpression, newExpression);

			if (newExpressionField != null) {
				newStatement = new CommonAssertStatement(this.getSource(),
						this.source(), newExpressionField, this.explanation);
				newStatement.setGuard(this.guard());
			} else {
				int numArgs = this.explanation.length;
				Expression[] newExplanation = Arrays.copyOf(this.explanation,
						numArgs);

				for (int i = 0; i < numArgs; i++) {
					Expression newArg = this.explanation[i].replaceWith(
							oldExpression, newExpression);

					if (newArg != null) {
						newExplanation[i] = newArg;
						newStatement = new CommonAssertStatement(
								this.getSource(), this.source(),
								this.condition, newExplanation);
						newStatement.setGuard(this.guard());
						break;
					}
				}
			}
		}
		return newStatement;
	}

	@Override
	public Set<Variable> variableAddressedOf(Scope scope) {
		Set<Variable> result = new HashSet<>();
		Set<Variable> subResult = condition.variableAddressedOf(scope);

		if (subResult != null)
			result.addAll(subResult);
		if (this.explanation != null)
			for (Expression arg : this.explanation) {
				subResult = arg.variableAddressedOf(scope);
				if (subResult != null)
					result.addAll(subResult);
			}
		return result;
	}

	@Override
	public Set<Variable> variableAddressedOf() {
		Set<Variable> result = new HashSet<>();
		Set<Variable> subResult = condition.variableAddressedOf();

		if (subResult != null)
			result.addAll(subResult);
		if (this.explanation != null)
			for (Expression arg : this.explanation) {
				subResult = arg.variableAddressedOf();
				if (subResult != null)
					result.addAll(subResult);
			}
		return result;
	}

	@Override
	public StatementKind statementKind() {
		return StatementKind.ASSERT;
	}

	@Override
	public Expression[] getExplanation() {
		return this.explanation;
	}
}
