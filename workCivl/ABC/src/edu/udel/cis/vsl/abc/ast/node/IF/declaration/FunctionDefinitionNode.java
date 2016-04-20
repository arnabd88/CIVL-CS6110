package edu.udel.cis.vsl.abc.ast.node.IF.declaration;

import edu.udel.cis.vsl.abc.ast.node.IF.statement.CompoundStatementNode;

/**
 * Represents a function definition, i.e., a function declaration which includes
 * the function body.
 * 
 * @author siegel
 * 
 */
public interface FunctionDefinitionNode extends FunctionDeclarationNode {

	/**
	 * Returns the body of the function, a compound statement.
	 * 
	 * @return the function body
	 */
	CompoundStatementNode getBody();

	/**
	 * Sets the body to the given statement. The statement becomes a child of
	 * this node.
	 * 
	 * @param statement
	 *            node to be made the body child of this node
	 */
	void setBody(CompoundStatementNode statement);

	@Override
	FunctionDefinitionNode copy();

}
