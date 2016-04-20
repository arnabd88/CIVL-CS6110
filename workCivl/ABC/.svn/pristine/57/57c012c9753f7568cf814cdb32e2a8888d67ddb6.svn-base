package edu.udel.cis.vsl.abc.ast.node.IF.expression;

import edu.udel.cis.vsl.abc.ast.node.IF.type.TypeNode;

/**
 * A C cast expression has the form <code>(typeName)expr</code>. The type to
 * which the expression is being cast (<code>typeName</code>) is obtained via
 * method {@link #getCastType()}.
 * 
 * See C11 Sec. 6.5.4.
 * 
 * @author siegel
 * 
 */
public interface CastNode extends ExpressionNode {

	/**
	 * Returns the node representing the type name in the cast expression
	 * 
	 * @return the node representing the type name
	 * @see #setCastType(TypeNode)
	 */
	TypeNode getCastType();

	/**
	 * Returns the node representing the expression argument of this cast
	 * expression.
	 * 
	 * @return the node for the expression being cast to a new type
	 * @see #setArgument(ExpressionNode)
	 */
	ExpressionNode getArgument();

	/**
	 * Sets the value that will be returned by {@link #getCastType()}.
	 * 
	 * @param type
	 *            the node representing the type name
	 */
	void setCastType(TypeNode type);

	/**
	 * Sets the value that will be returned by {@link #getArgument()}.
	 * 
	 * @param expression
	 *            the node for the expression being cast to a new type
	 */
	void setArgument(ExpressionNode expression);

	@Override
	CastNode copy();

}
