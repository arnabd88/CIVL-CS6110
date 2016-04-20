package edu.udel.cis.vsl.abc.ast.node.IF.type;

import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.VariableDeclarationNode;

public interface FunctionTypeNode extends TypeNode {

	boolean hasIdentifierList();

	/**
	 * The return type of this function. Non-null.
	 * 
	 * @return the return type
	 */
	TypeNode getReturnType();

	void setReturnType(TypeNode type);

	/**
	 * A function that takes a variable number of arguments will have an
	 * ellipsis occur at the end of its argument list.
	 * 
	 * @return true iff this function takes a variable number of arguments
	 */
	boolean hasVariableArgs();

	void setVariableArgs(boolean value);

	/**
	 * The sequence of formal parameter declarations for this function type. An
	 * identifier list is represented by a sequence of declarations in which all
	 * components other than the identifiers are null.
	 * 
	 * @return sequence of parameter declarations
	 */
	SequenceNode<VariableDeclarationNode> getParameters();

	void setParameters(SequenceNode<VariableDeclarationNode> parameters);

	@Override
	FunctionTypeNode copy();
}
