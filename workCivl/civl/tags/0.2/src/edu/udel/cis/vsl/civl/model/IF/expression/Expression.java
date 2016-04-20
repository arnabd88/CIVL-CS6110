/**
 * 
 */
package edu.udel.cis.vsl.civl.model.IF.expression;

import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.type.Type;

/**
 * The parent of all expressions.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public interface Expression {

	/**
	 * @return The highest scope accessed by this expression. Null if no
	 *         variables accessed.
	 */
	public Scope expressionScope();

	/**
	 * @param expressionScope
	 *            The highest scope accessed by this expression. Null if no
	 *            variables accessed.
	 */
	public void setExpressionScope(Scope expressionScope);

	/**
	 * 
	 * @return The type of this expression. For a primitive or variable, this is
	 *         the type of the primitive or variable. For a cast expression it
	 *         is the cast type. For operations it is the type of the operation
	 *         result.
	 */
	public Type getExpressionType();
}
