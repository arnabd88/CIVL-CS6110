/**
 * 
 */
package edu.udel.cis.vsl.civl.model.common.statement;

import java.util.ArrayList;

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
	private Expression expression;// the expression expected to be true
	private Expression[] printfArguments = null;

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
	 * @param source
	 *            The source location for this statement.
	 * @param expression
	 *            The expression being checked.
	 */
	public CommonAssertStatement(CIVLSource civlSource, Location source,
			Expression expression, ArrayList<Expression> arguments) {
		super(civlSource, source);
		this.expression = expression;
		this.printfArguments = new Expression[arguments.size()];
		arguments.toArray(printfArguments);
	}

	/**
	 * @param source
	 *            The source location for this statement.
	 * @param expression
	 *            The expression being checked.
	 */
	public CommonAssertStatement(CIVLSource civlSource, Location source,
			Expression expression, Expression[] arguments) {
		super(civlSource, source);
		this.expression = expression;
		this.printfArguments = arguments;
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
		String result = "$assert(" + expression;

		if (this.printfArguments != null) {
			for (Expression argument : this.printfArguments) {
				result += ", " + argument;
			}
		}
		result += ")";
		return result;
	}

	@Override
	public void calculateDerefs() {
		this.expression.calculateDerefs();
		this.hasDerefs = this.expression.hasDerefs();
		if(this.printfArguments != null){
			for(Expression arg : this.printfArguments){
				arg.calculateDerefs();
				this.hasDerefs = this.hasDerefs || arg.hasDerefs();
				if(this.hasDerefs)
					return;
			}
		}
	}

	@Override
	public void purelyLocalAnalysisOfVariables(Scope funcScope) {
		super.purelyLocalAnalysisOfVariables(funcScope);
		this.expression.purelyLocalAnalysisOfVariables(funcScope);
		if (this.printfArguments != null) {
			for (Expression arg : this.printfArguments) {
				arg.purelyLocalAnalysisOfVariables(funcScope);
			}
		}
	}

	@Override
	public void purelyLocalAnalysis() {
		this.guard().purelyLocalAnalysis();
		this.expression.purelyLocalAnalysis();
		if (!this.expression.isPurelyLocal()) {
			this.purelyLocal = false;
			return;
		}
		if (this.printfArguments != null) {
			for (Expression arg : this.printfArguments) {
				arg.purelyLocalAnalysis();
				if (!arg.isPurelyLocal()) {
					this.purelyLocal = false;
					return;
				}
			}
		}
		this.purelyLocal = this.guard().isPurelyLocal();
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
		if (this.printfArguments != null) {
			int number = printfArguments.length;

			for (int i = 0; i < number; i++) {
				Expression arg = printfArguments[i];

				if (arg == oldExpression) {
					printfArguments[i] = newExpression;
					return;
				}
				arg.replaceWith(oldExpression, newExpression);
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
					this.source(), this.expression);
			newStatement.setGuard(newGuard);
		} else {
			Expression newExpressionField = expression.replaceWith(
					oldExpression, newExpression);

			if (newExpressionField != null) {
				newStatement = new CommonAssertStatement(this.getSource(),
						this.source(), newExpressionField);
				newStatement.setGuard(this.guard());
			} else if (this.printfArguments != null) {
				boolean hasNewArg = false;
				int number = this.printfArguments.length;
				Expression[] newArgs = new Expression[number];

				for (int i = 0; i < number; i++) {
					if (hasNewArg)
						newArgs[i] = printfArguments[i];
					else {
						Expression newArg = printfArguments[i];

						newArg = newArg.replaceWith(oldExpression,
								newExpression);
						if (newArg != null) {
							newArgs[i] = newArg;
							hasNewArg = true;
						} else
							newArgs[i] = printfArguments[i];
					}
				}
				if (hasNewArg) {
					newStatement = new CommonAssertStatement(this.getSource(),
							this.source(), expression, newArgs);
					newStatement.setGuard(this.guard());
				}
			}
		}
		return newStatement;
	}

	@Override
	public Expression[] printfArguments() {
		return this.printfArguments;
	}

}
