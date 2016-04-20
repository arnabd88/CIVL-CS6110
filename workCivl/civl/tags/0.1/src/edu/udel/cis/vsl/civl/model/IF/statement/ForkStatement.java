/**
 * 
 */
package edu.udel.cis.vsl.civl.model.IF.statement;

import java.util.Vector;

import edu.udel.cis.vsl.civl.model.IF.expression.Expression;

/**
 * A fork statement.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public interface ForkStatement extends Statement {

	/**
	 * @return Expression for place where the process reference will be stored.
	 *         Null if non-existent.
	 */
	public Expression lhs();

	/**
	 * @return The function that is started in the new process.
	 */
	public Expression function();

	/**
	 * @return The arguments to the function.
	 */
	public Vector<Expression> arguments();

	/**
	 * @param lhs
	 *            Expression for place where the process reference will be
	 *            stored. Null if non-existent.
	 */
	public void setLhs(Expression lhs);

	/**
	 * @param function
	 *            The function that is started in the new process.
	 */
	public void setFunction(Expression function);

	/**
	 * @param arguments
	 *            The arguments to the function.
	 */
	public void setArguments(Vector<Expression> arguments);

}
