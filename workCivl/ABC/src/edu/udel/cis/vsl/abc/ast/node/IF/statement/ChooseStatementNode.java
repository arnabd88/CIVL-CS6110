package edu.udel.cis.vsl.abc.ast.node.IF.statement;

import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;

/**
 * A "choose" statement has the form "choose { s1 ... sn }", where each si is a
 * statement. It represents nondeterministic choice. Typically the si is a
 * "when" statement, but every statement has a guard, whether implicit or
 * explicit.
 * 
 * Basically wraps the sequence of statements s1, ..., sn.
 * 
 * @author siegel
 * 
 */
public interface ChooseStatementNode extends StatementNode,
		SequenceNode<StatementNode> {

	/**
	 * The default case is just some meta-data associated to the node, and is
	 * totally independent of the methods to create and add the children.
	 * 
	 * @param statement
	 */
	LabeledStatementNode getDefaultCase();

	/**
	 * The default case is just some meta-data associated to the node, and is
	 * totally independent of the methods to create and add the children.
	 * 
	 * @param statement
	 */
	void setDefaultCase(LabeledStatementNode statement);

	@Override
	ChooseStatementNode copy();

}
