/**
 * 
 */
package edu.udel.cis.vsl.civl.model.IF.statement;

import edu.udel.cis.vsl.civl.model.IF.expression.Expression;

/**
 * An assignment statement.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public interface AssignStatement extends Statement {

	/**
	 * @return The left hand side of the assignment.
	 */
	public Expression getLhs();

	/**
	 * @return The right hand side of the assignment.
	 */
	public Expression rhs();

	/**
	 * @param lhs
	 *            The left hand side of the assignment.
	 */
	public void setLhs(Expression lhs);

	/**
	 * @param rhs
	 *            The right hand side of the assignment.
	 */
	public void setRhs(Expression rhs);

}
