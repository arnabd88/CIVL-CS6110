package edu.udel.cis.vsl.abc.ast.node.IF.type;

import edu.udel.cis.vsl.abc.ast.node.IF.IdentifierNode;
import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.DeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.EnumeratorDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.BlockItemNode;
import edu.udel.cis.vsl.abc.ast.type.IF.EnumerationType;

/**
 * An enumeration type.
 * 
 * @author siegel
 */
public interface EnumerationTypeNode extends DeclarationNode, TypeNode,
		BlockItemNode {
	/**
	 * Returns the "tag", which is the name of this enumerated type. For
	 * example, in "enum color {...}", "color" is the tag.
	 * 
	 * @return the tag of this enumerated type
	 */
	IdentifierNode getTag();

	/**
	 * Returns the sequence of enumerators for this enumerated type. Each
	 * enumerator consists of a name and optional constant expression. If the
	 * optional constant expression is absent, it will be null.
	 * 
	 * @return the sequence node for the enumerators of this type
	 */
	SequenceNode<EnumeratorDeclarationNode> enumerators();

	@Override
	EnumerationTypeNode copy();

	/**
	 * Nullifies the enumerators field, making this an incomplete enumeration
	 * type. If already null, it is a no-op.
	 */
	void makeIncomplete();

	@Override
	EnumerationType getType();
}
