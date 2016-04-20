/**
 * 
 */
package edu.udel.cis.vsl.civl.model.IF.statement;


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
}
