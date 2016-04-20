/**
 * 
 */
package edu.udel.cis.vsl.civl.model.IF.statement;

import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.LHSExpression;

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
	LHSExpression getLhs();

	/**
	 * @return The right hand side of the assignment.
	 */
	Expression rhs();

	/**
	 * @param lhs
	 *            The left hand side of the assignment.
	 */
	void setLhs(LHSExpression lhs);

	/**
	 * @param rhs
	 *            The right hand side of the assignment.
	 */
	void setRhs(Expression rhs);

	/**
	 * 
	 * @return True iff this assignment is used to initialize a variable
	 *         translated from a variable declaration, e.g., int x = 0.
	 */
	boolean isInitialization();

	/**
	 * Mark an assignment statement to be an initialization or not.
	 * 
	 * @param value
	 *            True iff want to mark the assignment as an initialization,
	 *            otherwise false.
	 */
	void setInitialization(boolean value);

}
