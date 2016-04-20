/**
 * 
 */
package edu.udel.cis.vsl.civl.model.common.statement;

import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.AssignStatement;

/**
 * An assignment statement.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public class CommonAssignStatement extends CommonStatement implements AssignStatement {

	private Expression lhs;
	private Expression rhs;

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
	public CommonAssignStatement(Location source, Expression lhs, Expression rhs) {
		super(source);
		this.lhs = lhs;
		this.rhs = rhs;
	}

	/**
	 * @return The left hand side of the assignment.
	 */
	public Expression getLhs() {
		return lhs;
	}

	/**
	 * @return The right hand side of the assignment.
	 */
	public Expression rhs() {
		return rhs;
	}

	/**
	 * @param lhs
	 *            The left hand side of the assignment.
	 */
	public void setLhs(Expression lhs) {
		this.lhs = lhs;
	}

	/**
	 * @param rhs
	 *            The right hand side of the assignment.
	 */
	public void setRhs(Expression rhs) {
		this.rhs = rhs;
	}

	@Override
	public String toString() {
		return lhs + " = " + rhs;
	}

}
