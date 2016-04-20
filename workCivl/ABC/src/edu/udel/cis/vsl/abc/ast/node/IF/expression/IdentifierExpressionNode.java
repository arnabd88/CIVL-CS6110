package edu.udel.cis.vsl.abc.ast.node.IF.expression;

import edu.udel.cis.vsl.abc.ast.node.IF.IdentifierNode;

/**
 * Represents the use of an identifier as an expression. The name of a variable
 * or function are the two most common uses. This class basically wraps a
 * {@link IdentifierNode}.
 * 
 * @author siegel
 * 
 */
public interface IdentifierExpressionNode extends ExpressionNode {

	/**
	 * Returns the identifier node child of this node.
	 * 
	 * @return the identifier node
	 */
	IdentifierNode getIdentifier();

	/**
	 * Sets the value returned by {@link #getIdentifier()}.
	 * 
	 * @param identifier
	 *            the identifier node
	 */
	void setIdentifier(IdentifierNode identifier);

	@Override
	IdentifierExpressionNode copy();

}
