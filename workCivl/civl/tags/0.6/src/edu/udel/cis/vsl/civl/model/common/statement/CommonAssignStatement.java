/**
 * 
 */
package edu.udel.cis.vsl.civl.model.common.statement;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.ConditionalExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.LHSExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.VariableExpression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.AssignStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;

/**
 * An assignment statement.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public class CommonAssignStatement extends CommonStatement implements
		AssignStatement {

	private LHSExpression lhs;
	private Expression rhs;
	private boolean isInitialization;

	/**
	 * An assignment statement.
	 * 
	 * @param source
	 *            The source location for this statement.
	 * @param lhs
	 *            The left hand side of the assignment.
	 * @param rhs
	 *            The right hand side of the assignment.
	 */
	public CommonAssignStatement(CIVLSource civlSource, Location source,
			LHSExpression lhs, Expression rhs) {
		super(civlSource, source);
		this.lhs = lhs;
		this.rhs = rhs;
		this.isInitialization = false;
	}

	/**
	 * @return The left hand side of the assignment.
	 */
	@Override
	public LHSExpression getLhs() {
		return lhs;
	}

	/**
	 * @return The right hand side of the assignment.
	 */
	@Override
	public Expression rhs() {
		return rhs;
	}

	/**
	 * @param lhs
	 *            The left hand side of the assignment.
	 */
	@Override
	public void setLhs(LHSExpression lhs) {
		this.lhs = lhs;
	}

	/**
	 * @param rhs
	 *            The right hand side of the assignment.
	 */
	@Override
	public void setRhs(Expression rhs) {
		this.rhs = rhs;
	}

	@Override
	public String toString() {
		return lhs + " = " + rhs;
	}

	@Override
	public void calculateDerefs() {
		this.lhs.calculateDerefs();
		this.rhs.calculateDerefs();
		this.hasDerefs = this.lhs.hasDerefs() || this.rhs.hasDerefs();
	}

	@Override
	public void purelyLocalAnalysisOfVariables(Scope funcScope) {
		super.purelyLocalAnalysisOfVariables(funcScope);
		this.lhs.purelyLocalAnalysisOfVariables(funcScope);
		this.rhs.purelyLocalAnalysisOfVariables(funcScope);
	}

	/**
	 * {@inheritDoc} If this is an initialization assignment, this assignment
	 * can be considered as purely local even if the LHS variable is not purely
	 * local. For most cases, the RHS is a constant and thus the initialization
	 * of a variable would be considered as purely local.
	 */
	@Override
	public void purelyLocalAnalysis() {
		this.guard().purelyLocalAnalysis();
		this.lhs.purelyLocalAnalysis();
		this.rhs.purelyLocalAnalysis();
		if (this.isInitialization) {
			this.purelyLocal = this.guard().isPurelyLocal()
					&& this.rhs.isPurelyLocal();
		} else {
			this.purelyLocal = this.guard().isPurelyLocal()
					&& this.lhs.isPurelyLocal() && this.rhs.isPurelyLocal();
		}
	}

	@Override
	public void replaceWith(ConditionalExpression oldExpression,
			VariableExpression newExpression) {
		super.replaceWith(oldExpression, newExpression);
		if (rhs == oldExpression) {
			rhs = newExpression;
			return;
		}
		this.rhs.replaceWith(oldExpression, newExpression);
	}

	@Override
	public Statement replaceWith(ConditionalExpression oldExpression,
			Expression newExpression) {
		Expression newGuard = guardReplaceWith(oldExpression, newExpression);
		CommonAssignStatement newStatement = null;

		if (newGuard != null) {
			newStatement = new CommonAssignStatement(this.getSource(),
					this.source(), lhs, this.rhs);
			newStatement.setGuard(newGuard);
		} else {
			Expression newRhs = rhs.replaceWith(oldExpression, newExpression);

			if (newRhs != null) {
				newStatement = new CommonAssignStatement(this.getSource(),
						this.source(), lhs, newRhs);
				newStatement.setGuard(this.guard());
			}
		}
		return newStatement;
	}

	@Override
	public boolean isInitialization() {
		return this.isInitialization;
	}

	@Override
	public void setInitialization(boolean value) {
		this.isInitialization = value;
	}
}