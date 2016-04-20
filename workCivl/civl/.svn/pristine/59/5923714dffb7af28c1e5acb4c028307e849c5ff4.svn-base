/**
 * 
 */
package edu.udel.cis.vsl.civl.model.common.statement;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.LHSExpression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.AssignStatement;

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

}
