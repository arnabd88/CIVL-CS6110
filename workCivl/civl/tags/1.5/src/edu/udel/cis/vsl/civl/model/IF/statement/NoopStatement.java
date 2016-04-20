/**
 * 
 */
package edu.udel.cis.vsl.civl.model.IF.statement;

import edu.udel.cis.vsl.civl.model.IF.expression.Expression;

/**
 * Marker interface for a noop statement.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public interface NoopStatement extends Statement {

	public enum NoopKind {
		IF_ELSE, SWITCH, LOOP, NONE, GOTO, ATOMIC_ATOM
	}

	/**
	 * Returns the kind of this noop statement, which might be a if-else
	 * branching, loop branching, atomic entering/exiting noop statement, etc.
	 * 
	 * @return The kind of this noop statement
	 */
	NoopKind noopKind();

	Expression expression();

	/**
	 * is this a temporary noop that is inserted by the model builder and should
	 * be removed from the model?
	 * 
	 * @return
	 */
	boolean isTemporary();

	void setRemovable();

	boolean isRemovable();

	/**
	 * is this noop associating to a variable declaration?
	 * 
	 * @return
	 */
	boolean isVariableDeclaration();
}
