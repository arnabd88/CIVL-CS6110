package edu.udel.cis.vsl.abc.ast.node.IF.expression;

import edu.udel.cis.vsl.abc.ast.node.IF.IdentifierNode;

/**
 * An enumeration constant node represents a use of an enumeration constant as
 * an expression. It wraps an identifier node.
 * 
 * @author siegel
 * 
 */
public interface EnumerationConstantNode extends ConstantNode {

	/**
	 * Returns the underlying identifier node.
	 * 
	 * @return the underlying identifier node which is the name of the
	 *         enumeration constant
	 */
	IdentifierNode getName();

	/**
	 * Sets the value returned by {@link #getName()}.
	 * 
	 * @param name
	 *            the underlying identifier node which is the name of the
	 *            enumeration constant
	 */
	void setName(IdentifierNode name);

	@Override
	EnumerationConstantNode copy();

}
