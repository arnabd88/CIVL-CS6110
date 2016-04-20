package edu.udel.cis.vsl.abc.ast.node.IF.statement;

/**
 * An atomic node represents a CIVL-C <code>$atomic</code> or <code>$atom</code>
 * statement. Note that <code>$atomic</code> places no restrictions on its
 * statement body, while <code>$atom</code> requires that any execution of its
 * body be finite, non-blocking, and deterministic.
 * 
 * @author Manchun Zheng (zmanchun)
 * 
 */
public interface AtomicNode extends StatementNode {

	@Override
	AtomicNode copy();

	/**
	 * The body of the <code>$atomic</code> or <code>$atom</code> statement.
	 * 
	 * @return the body of the atomic statement
	 */
	StatementNode getBody();

	/**
	 * Sets the body of this atomic statement.
	 * 
	 * @param body
	 *            a statement to become the body
	 */
	void setBody(StatementNode body);

	/**
	 * Is this an <code>$atom</code> statement?
	 * 
	 * @return <code>true</code> if this is an <code>$atom</code> statement;
	 *         <code>false</code> if this is an <code>$atomic</code> statement
	 */
	boolean isAtom();
}
