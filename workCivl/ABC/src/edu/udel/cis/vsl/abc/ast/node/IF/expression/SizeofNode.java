package edu.udel.cis.vsl.abc.ast.node.IF.expression;

/**
 * Represents a C <code>sizeof(...)</code> expression. The argument can be
 * either an expression or a type name. The interface {@link SizeableNode} is
 * used to include both expression and type nodes, so the argument is
 * represented by a node implementing that interface.
 * 
 * @author siegel
 * 
 */
public interface SizeofNode extends ExpressionNode {

	/**
	 * The object that we taking the size of. It is either a type or an
	 * expression.
	 * 
	 * @return the argument of the <code>sizeof</code> expression
	 */
	SizeableNode getArgument();

	/**
	 * Sets the value returned by {@link #getArgument()}.
	 * 
	 * @param argument
	 *            the argument
	 */
	void setArgument(SizeableNode argument);

	@Override
	SizeofNode copy();
}
