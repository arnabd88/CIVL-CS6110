package edu.udel.cis.vsl.abc.ast.node.IF.expression;

import edu.udel.cis.vsl.abc.ast.node.IF.IdentifierNode;

/**
 * A C expression in which the operator is the <code>.</code> (dot) operator,
 * used to specify a member of a structure or union.
 * 
 * @author siegel
 * 
 */
public interface DotNode extends ExpressionNode {

	/**
	 * Returns the node representing the left operand, which must have structure
	 * or union type.
	 * 
	 * @return the left operand
	 */
	ExpressionNode getStructure();

	/**
	 * Sets the value returned by {@link #getStructure()}.
	 * 
	 * @param structure
	 *            the left operand
	 */
	void setStructure(ExpressionNode structure);

	/**
	 * Returns the node representing the right operand, which must be an
	 * identifier which names a field in the structure or union type which is
	 * the type of the left operand.
	 * 
	 * @return the right operand
	 */
	IdentifierNode getFieldName();

	/**
	 * Sets the value returned by {@link #getFieldName()}.
	 * 
	 * @param field
	 *            the right operand
	 */
	void setFieldName(IdentifierNode field);

	@Override
	DotNode copy();

}
