package edu.udel.cis.vsl.abc.ast.node.IF.expression;

import edu.udel.cis.vsl.abc.ast.node.IF.compound.CompoundInitializerNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.TypeNode;

/**
 * <p>
 * Compound literals are used to represent literal array, structure, and union
 * values. See C11 Sec. 6.5.2.5 and Sec. 6.7.9.
 * </p>
 * 
 * <p>
 * The syntax and interpretation of compound literals is exactly the same as for
 * those of compound initializers. The only difference is that for compound
 * initializers, the type is obtained from the declared type of the variable
 * being initialized, while for compound literals the type is obtained by
 * placing the type name in parentheses before the initialization list (similar
 * in appearance to a cast).
 * </p>
 * 
 * @author siegel
 * 
 */
public interface CompoundLiteralNode extends ExpressionNode {

	/**
	 * Gets the type node for the type name placed in parentheses before the
	 * initializer list.
	 * 
	 * @return the type node
	 */
	TypeNode getTypeNode();

	/**
	 * Returns the initializer list, which is exactly the same structure used in
	 * a compound initializer.
	 * 
	 * @return the initializer list
	 */
	CompoundInitializerNode getInitializerList();

	/**
	 * Sets the initializer list.
	 * 
	 * @param arg
	 *            the compound initializer node to become the child of this node
	 */
	void setInitializerList(CompoundInitializerNode arg);

	@Override
	CompoundLiteralNode copy();

}
