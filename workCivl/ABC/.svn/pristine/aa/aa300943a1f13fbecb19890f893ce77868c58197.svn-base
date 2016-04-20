package edu.udel.cis.vsl.abc.ast.node.IF.omp;

import edu.udel.cis.vsl.abc.ast.node.IF.IdentifierNode;
import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.IdentifierExpressionNode;

/**
 * This interface stands for synchronization constructs of OpenMP, including:
 * <ol>
 * <li>master</li>
 * <li>critical</li>
 * <li>barrier</li>
 * <li>flush</li>
 * <li>atomic</li>
 * </ol>
 * 
 * Currently, taskwait and atomic constructs are not supported.
 * 
 * @author Manchun Zheng
 * 
 */
public interface OmpSyncNode extends OmpExecutableNode {
	/**
	 * The kind of this OmpSyncNode:
	 * 
	 * <ul>
	 * <li>MASTER: the master construct</li>
	 * <li>CRITICAL: the critical construct</li>
	 * <li>BARRIER: the barrier construct</li>
	 * <li>FLUSH: the flush construct</li>
	 * <li>ORDERED: the ordered construct</li>
	 * </ul>
	 * 
	 * @author Manchun Zheng
	 * 
	 */
	public enum OmpSyncNodeKind {
		MASTER, CRITICAL, BARRIER, FLUSH, ORDERED, OMPATOMIC
	}

	/**
	 * Returns the kind of this OpenMP synchronization construct.
	 * 
	 * @return the synchronization kind of this node.
	 */
	OmpSyncNodeKind ompSyncNodeKind();

	/**
	 * Updates the name declared by the critical construct. Only valid when the
	 * synchronization kind of this node is OmpSyncNodeKind.CRITICAL.
	 * 
	 * @param name
	 *            The name declared by the critical construct.
	 */
	void setCriticalName(IdentifierNode name);

	/**
	 * The identifier node representing the name of the critical section, only
	 * valid for CRITICAL kind.
	 * 
	 * @return the identifier node representing the name of the critical
	 *         section, only valid for CRITICAL kind.
	 */
	IdentifierNode criticalName();

	/**
	 * The list of variables in the flush construct. NULL for other kinds.
	 * 
	 * @return the list of variables in the flush construct, NULL for other
	 *         kinds.
	 */
	SequenceNode<IdentifierExpressionNode> flushedList();

	/**
	 * Updates the flush list of this construct. Only valid when the
	 * synchronization kind of this node is OmpSyncNodeKind.FLUSH.
	 * 
	 * @param list
	 *            The new flush list.
	 */
	void setFlushedList(SequenceNode<IdentifierExpressionNode> list);
}
