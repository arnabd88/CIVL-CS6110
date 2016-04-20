package edu.udel.cis.vsl.abc.ast.node.IF.acsl;

import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;

/**
 * An ACSL <code>assigns</code> or ACSL-CIVLC <code>reads</code> clause
 * specifies a set of existing memory units. The claim is that if an existing
 * memory unit is not in the set, it will not be modified in the course of the
 * function call. The syntax is:
 * 
 * <pre>
 * assigns <memory-list>;
 * </pre>
 * 
 * or
 * 
 * <pre>
 * reads <memory-list>;
 * </pre>
 * 
 * where <code>memory-list</code> is a comma-separated list of expressions of
 * type $memory.
 *
 * @see ContractNode
 * 
 * @author Manchun Zheng
 * 
 */
public interface AssignsOrReadsNode extends ContractNode {

	/**
	 * Gets the list of memory associated with this node.
	 * 
	 * @return the list of memory associated with this node.
	 */
	SequenceNode<ExpressionNode> getMemoryList();

	@Override
	AssignsOrReadsNode copy();

	/**
	 * Is this an <code>assigns</code> clause?
	 * 
	 * @return
	 */
	boolean isAssigns();

	/**
	 * Is this a <code>reads</code> clause?
	 * 
	 * @return
	 */
	boolean isReads();
}
