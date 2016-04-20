package edu.udel.cis.vsl.abc.ast.node.IF.statement;

import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.ContractNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;

/**
 * Root of type hierarchy for every kind of loop statement. Every such statement
 * has at least a condition specifying when to stay in the loop, and a body.
 * 
 * @author siegel
 * 
 */
public interface LoopNode extends StatementNode {

	public static enum LoopKind {
		WHILE, DO_WHILE, FOR
	};

	/**
	 * The condition which controls when to stay in or exit the loop. For WHILE
	 * and FOR loops, evaluated before entering body; for DO_WHILE, evaluated
	 * after each execution of body.
	 * 
	 * @return the loop condition
	 */
	ExpressionNode getCondition();

	/**
	 * Sets the loop condition for this loop node.
	 * 
	 * @param condition
	 *            the loop condition
	 */
	void setCondition(ExpressionNode condition);

	/**
	 * The loop body.
	 * 
	 * @return the loop body
	 */
	StatementNode getBody();

	/**
	 * Sets the loop body.
	 * 
	 * @param body
	 *            the body
	 */
	void setBody(StatementNode body);

	/**
	 * What kind of loop is this?
	 * 
	 * @return the loop kind
	 */
	LoopKind getKind();

	SequenceNode<ContractNode> loopContracts();

	@Override
	LoopNode copy();

}
