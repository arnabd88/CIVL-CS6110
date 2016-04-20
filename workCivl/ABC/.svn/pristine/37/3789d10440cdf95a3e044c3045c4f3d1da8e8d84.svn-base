package edu.udel.cis.vsl.abc.ast.node.IF.acsl;

import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.VariableDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;

/**
 * A memory set node represents a set of memory locations. The syntax could be:
 * 
 * <pre>
 * { tset | binders (; pred)? }
 * </pre>
 * 
 * or
 * 
 * <pre>
 * { term }
 * </pre>
 * 
 * @author Manchun Zheng
 *
 */
public interface MemorySetNode extends ExpressionNode {

	/**
	 * the elements of this set
	 * 
	 * @return
	 */
	ExpressionNode getElements();

	/**
	 * The binders of this set; could be null.
	 * 
	 * @return
	 */
	SequenceNode<VariableDeclarationNode> getBinders();

	/**
	 * The predicate of this set; could be null.
	 * 
	 * @return
	 */
	ExpressionNode getPredicate();

	@Override
	MemorySetNode copy();

}
