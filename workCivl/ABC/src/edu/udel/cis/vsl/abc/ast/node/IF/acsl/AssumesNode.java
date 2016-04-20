package edu.udel.cis.vsl.abc.ast.node.IF.acsl;

import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;

/**
 * This represents an ACSL <code>assumes</code> clause, which has the following
 * syntax:
 * 
 * <pre>
 * assumes predicate;
 * </pre>
 * 
 * @author Manchun Zheng
 *
 */
public interface AssumesNode extends ContractNode {
	/**
	 * returns the predicate of this <code>assumes</code> clause.
	 * 
	 * @return
	 */
	ExpressionNode getPredicate();

	@Override
	AssumesNode copy();
}
