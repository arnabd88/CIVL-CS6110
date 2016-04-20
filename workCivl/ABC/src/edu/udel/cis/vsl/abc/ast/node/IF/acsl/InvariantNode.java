package edu.udel.cis.vsl.abc.ast.node.IF.acsl;

import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;

public interface InvariantNode extends ContractNode {
	/**
	 * Returns the expression of this invariant
	 * 
	 * @return
	 */
	ExpressionNode getExpression();

	/**
	 * is this a loop invariant?
	 * 
	 * @return
	 */
	boolean isLoopInvariant();

	@Override
	InvariantNode copy();
}
