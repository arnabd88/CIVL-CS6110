/**
 * 
 */
package edu.udel.cis.vsl.civl.model.IF.statement;

import java.util.Vector;

import edu.udel.cis.vsl.civl.model.IF.Function;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;

/**
 * A function call. Either of the form f(x) or else v=f(x).
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public interface CallStatement extends Statement {

	/**
	 * @return The left hand side expression if applicable. Else null.
	 */
	public Expression lhs();

	/**
	 * @return The function being called.
	 */
	public Function function();

	/**
	 * @return The arguments to the function.
	 */
	public Vector<Expression> arguments();

	/**
	 * @param lhs
	 *            The left hand side expression if applicable. Else null.
	 */
	public void setLhs(Expression lhs);

	/**
	 * @param function
	 *            The function being called.
	 */
	public void setFunction(Function function);

	/**
	 * @param arguments
	 *            The arguments to the function.
	 */
	public void setArguments(Vector<Expression> arguments);

}
