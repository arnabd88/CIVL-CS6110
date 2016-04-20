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
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.model.IF.statement.WaitStatement;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

/**
 * A wait statement, to wait for another process to complete.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public class CommonWaitStatement extends CommonStatement implements
		WaitStatement {

	private Expression process;

	/**
	 * A join statement, to wait for another process to complete.
	 * 
	 * @param source
	 *            The source location for this join.
	 * @param process
	 *            A reference to the process.
	 */
	public CommonWaitStatement(CIVLSource civlSource, Location source,
			Expression process) {
		super(civlSource, source);
		this.process = process;
	}

	/**
	 * @return The process.
	 */
	@Override
	public Expression process() {
		return process;
	}

	/**
	 * @param process
	 *            The process.
	 */
	@Override
	public void setProcess(Expression process) {
		this.process = process;
	}

	@Override
	public String toString() {
		return "wait " + process;
	}

	@Override
	public void calculateDerefs() {
		this.process.calculateDerefs();
		this.hasDerefs = this.process.hasDerefs();
	}

	@Override
	public void purelyLocalAnalysisOfVariables(Scope funcScope) {
		super.purelyLocalAnalysisOfVariables(funcScope);
		this.process.purelyLocalAnalysisOfVariables(funcScope);
	}

	@Override
	public void purelyLocalAnalysis() {
		// For most cases, wait statement is blocked and thus is considered
		// as not purely local
		this.purelyLocal = false;
	}

	@Override
	public void replaceWith(ConditionalExpression oldExpression,
			VariableExpression newExpression) {
		super.replaceWith(oldExpression, newExpression);

		if (process == oldExpression) {
			process = newExpression;
			return;
		}

		this.process.replaceWith(oldExpression, newExpression);
	}

	@Override
	public Statement replaceWith(ConditionalExpression oldExpression,
			Expression newExpression) {
		Expression newGuard = guardReplaceWith(oldExpression, newExpression);
		CommonAssertStatement newStatement = null;

		if (newGuard != null) {
			newStatement = new CommonAssertStatement(this.getSource(),
					this.source(), this.process);
			newStatement.setGuard(newGuard);
		} else {
			Expression newProcessExpression = process.replaceWith(
					oldExpression, newExpression);

			if (newProcessExpression != null) {
				newStatement = new CommonAssertStatement(this.getSource(),
						this.source(), newProcessExpression);
				newStatement.setGuard(this.guard());
			}
		}
		return newStatement;
	}

	@Override
	public Set<Variable> variableAddressedOf(Scope scope) {
		return process.variableAddressedOf(scope);
	}

	@Override
	public Set<Variable> variableAddressedOf() {
		return process.variableAddressedOf();
	}

	@Override
	public StatementKind statementKind() {
		return StatementKind.WAIT;
	}

}
