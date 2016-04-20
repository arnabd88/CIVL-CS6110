package edu.udel.cis.vsl.abc.ast.node.IF.acsl;

import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;

/**
 * This represents a <code>guards</code> clause that specifies a guard for a
 * function. The function may be a system or ordinary function. It has the
 * syntax <code>guards <bool-expr> ;</code>.
 * 
 * @author Manchun Zheng
 *
 */
public interface GuardsNode extends ContractNode {
	/**
	 * Gets the boolean expression of this guard.
	 * 
	 * @return
	 */
	ExpressionNode getExpression();

	@Override
	GuardsNode copy();
}
