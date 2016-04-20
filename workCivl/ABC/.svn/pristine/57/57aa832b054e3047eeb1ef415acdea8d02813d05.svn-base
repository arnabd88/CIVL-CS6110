package edu.udel.cis.vsl.abc.ast.node.IF.declaration;

import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.BlockItemNode;

/**
 * <p>
 * A CIVL-C scope-parameterized declaration node. Certain declarations can be
 * parameterized by scopes. These declarations involve a sequence of formal
 * scope parameters. Those formals can then be used in the "body" of the
 * declaration.
 * </p>
 * 
 * <p>
 * Will be deprecated soon.
 * </p>
 * 
 * @author siegel
 * 
 */
public interface ScopeParameterizedDeclarationNode extends DeclarationNode,
		BlockItemNode {

	/**
	 * Returns the scope parameters. These are represented as a sequence of
	 * variable declaration nodes. This sequence is child 0 of this AST node.
	 * 
	 * @return the scope parameters; child 0 of this node
	 */
	SequenceNode<VariableDeclarationNode> parameters();

	/**
	 * Returns the base declaration, the "body" of this parameterized
	 * declaration. This is child 1 of this AST node.
	 * 
	 * @return the base declaration; child 1 of this node
	 */
	DeclarationNode baseDeclaration();

	ScopeParameterizedDeclarationNode copy();

}
