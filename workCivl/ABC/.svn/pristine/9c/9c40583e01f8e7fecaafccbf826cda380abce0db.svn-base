package edu.udel.cis.vsl.abc.ast.node.IF.acsl;

import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;

/**
 * A <code>requires</code> clause in a CIVL-C procedure contract. This clause
 * specifies a pre-condition: something that is expected to hold when the
 * function is called.
 * 
 * @see EnsuresNode
 * @see ContractNode
 * 
 * @author siegel
 * 
 */
public interface RequiresNode extends ContractNode {

	/**
	 * Gets the boolean condition which is the pre-condition.
	 * 
	 * @return the boolean expression which specified the pre-condition
	 */
	ExpressionNode getExpression();

	@Override
	RequiresNode copy();

}
