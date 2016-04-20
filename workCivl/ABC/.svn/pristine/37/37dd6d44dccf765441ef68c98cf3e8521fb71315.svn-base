package edu.udel.cis.vsl.abc.ast.node.IF.expression;

import edu.udel.cis.vsl.abc.ast.node.IF.IdentifierNode;

/**
 * An expression in which the operator is the C <code>-></code> (arrow)
 * operator. In C, <code>e->f</code> is equivalent to <code>(*e).f</code>.
 * 
 * @author siegel
 * 
 */
public interface ArrowNode extends ExpressionNode {

	/**
	 * Returns the node representing the left argument of the arrow operator.
	 * That argument is an expression which is a pointer to a structure or
	 * union.
	 * 
	 * @return the left argument of the arrow operator
	 * @see #setStructurePointer(ExpressionNode)
	 */
	ExpressionNode getStructurePointer();

	/**
	 * Sets the value that will be returned by {@link #getStructurePointer()}.
	 * 
	 * @param structure
	 *            the left argument of the arrow operator
	 */
	void setStructurePointer(ExpressionNode structure);

	/**
	 * Returns the node for the right argument of the arrow operator. That
	 * argument is an identifier which names a field in the structure or union.
	 * 
	 * @return the right argument of the arrow operator
	 * @see #setFieldName(IdentifierNode)
	 */
	IdentifierNode getFieldName();

	/**
	 * Sets the value that will be returned by {@link #getFieldName()}.
	 * 
	 * @param field
	 *            the right argument of the arrow operator
	 */
	void setFieldName(IdentifierNode field);

	@Override
	ArrowNode copy();

}
