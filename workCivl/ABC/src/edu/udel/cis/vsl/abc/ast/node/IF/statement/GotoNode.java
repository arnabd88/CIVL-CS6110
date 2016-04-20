package edu.udel.cis.vsl.abc.ast.node.IF.statement;

import edu.udel.cis.vsl.abc.ast.node.IF.IdentifierNode;

/**
 * Represents a C "goto labelName;" statement.
 * 
 * @author siegel
 * 
 */
public interface GotoNode extends JumpNode {

	/**
	 * Returns the name of the label to which to go. From this identifier, one
	 * can get the underlying Label entity.
	 * 
	 * @return the label identifier node
	 */
	IdentifierNode getLabel();

	@Override
	GotoNode copy();

}
