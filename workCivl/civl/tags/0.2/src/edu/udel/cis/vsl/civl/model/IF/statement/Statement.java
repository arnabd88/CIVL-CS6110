/**
 * 
 */
package edu.udel.cis.vsl.civl.model.IF.statement;

import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;

/**
 * The parent of all statements.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public interface Statement {

	/**
	 * @return The location that is the source of this statement.
	 */
	public Location source();

	/**
	 * @return The location that is the target of this statement.
	 */
	public Location target();

	/**
	 * @return The boolean-valued guard expression for this statement.
	 */
	public Expression guard();

	/**
	 * @param source
	 *            the source to set
	 */
	public void setSource(Location source);

	/**
	 * @param target
	 *            the target to set
	 */
	public void setTarget(Location target);

	/**
	 * @param guard
	 *            the guard to set
	 */
	public void setGuard(Expression guard);

	/**
	 * @return The highest scope accessed by this statement. Null if no
	 *         variables accessed.
	 */
	public Scope statementScope();

	/**
	 * @param statementScope
	 *            The highest scope accessed by this statement. Null if no
	 *            variables accessed.
	 */
	public void setStatementScope(Scope statementScope);


}
