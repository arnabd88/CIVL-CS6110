package edu.udel.cis.vsl.abc.ast.node.IF.declaration;

import edu.udel.cis.vsl.abc.ast.entity.IF.Typedef;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.BlockItemNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.TypeNode;

/**
 * A node representing a typedef declaration. The identifier node in this
 * declaration is the name of the typedef. The other child is a type node, which
 * is the type being assigned to that identifier.
 * 
 * @author siegel
 * 
 */
public interface TypedefDeclarationNode extends DeclarationNode, BlockItemNode {

	/**
	 * Returns the typedef entity itself associated to this declaration.
	 * 
	 * @return the typedef
	 */
	@Override
	Typedef getEntity();

	/**
	 * Returns the AST node for the type that is being associated to the typedef
	 * name.
	 * 
	 * @return the type assigned to this typedef name
	 */
	TypeNode getTypeNode();

	/**
	 * Sets the type node child of this typedef declaration node.
	 * 
	 * @param type
	 *            the type node to be made a child of this node
	 */
	void setTypeNode(TypeNode type);

	@Override
	TypedefDeclarationNode copy();
}
