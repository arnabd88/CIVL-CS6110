package edu.udel.cis.vsl.abc.ast.node.IF.expression;

import edu.udel.cis.vsl.abc.ast.node.IF.type.TypeNode;

/**
 * The <code>_Alignof(typename)</code> operator. See C11 Sec. 6.5.3.4. Results
 * in an integer constant.
 * 
 * @author siegel
 * 
 */
public interface AlignOfNode extends ExpressionNode {

	/**
	 * Gets node representing the argument of the <code>_Alignof</code>
	 * operator.
	 * 
	 * @return the node representing the type name which is the argument of this
	 *         operator
	 */
	TypeNode getArgument();

	/**
	 * Sets the argument that will be returned by {@link #getArgument()}.
	 * 
	 * @param type
	 *            the type node representing the type name argument of this
	 *            operator
	 */
	void setArgument(TypeNode type);

	@Override
	AlignOfNode copy();

}
