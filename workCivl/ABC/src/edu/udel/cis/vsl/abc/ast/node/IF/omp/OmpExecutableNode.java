package edu.udel.cis.vsl.abc.ast.node.IF.omp;

import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.IdentifierExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.StatementNode;

/**
 * Represents an OpenMP executable Construct.<br>
 * The children of an OmpStatementNode are:
 * <ul>
 * <li>SequenceNode&lt;IdentifierExpressionNode&gt; "sharedList", the list of
 * identifiers declared by <code>shared</code></li>
 * <li>SequenceNode&lt;IdentifierExpressionNode&gt; "privateList", the list of
 * identifiers declared by <code>private</code></li>
 * <li>SequenceNode&lt;IdentifierExpressionNode&gt; "firstprivateList", the list
 * of identifiers declared by <code>firstprivate</code></li>
 * <li>SequenceNode&lt;IdentifierExpressionNode&gt; "lastprivateList", the list
 * of identifiers declared by <code>lastprivate</code></li>
 * <li>SequenceNode&lt;IdentifierExpressionNode&gt; "copyinList", the list of
 * identifiers declared by <code>copyin</code></li>
 * <li>SequenceNode&lt;IdentifierExpressionNode&gt; "copyprivateList", the list
 * of identifiers declared by <code>copyprivate</code></li>
 * <li>SequenceNode&lt;OmpReductionNode&gt; "reductionList", the list of
 * operators and identifiers declared by <code>reduction</code></li>
 * <li>StatementNode, the statement node affected by this pragma</li>.
 * </ul>
 * In the constructor, these children are all set to null.
 * 
 */
public interface OmpExecutableNode extends OmpNode, StatementNode {

	/**
	 * The kind of this OpenMP statement:
	 * <ul>
	 * <li>PARALLEL: the parallel constuct</li>
	 * <li>SYNCHRONIZATION: synchronization constructs such as master, critical,
	 * barrier, taskwait, taskgroup, atomic, flush, ordered, etc.</li>
	 * <li>WORKSHARING: worksharing constructs such as sections (section) and
	 * single.</li>
	 * </ul>
	 * 
	 * @author Manchun Zheng
	 * 
	 */
	public enum OmpExecutableKind {
		PARALLEL, SYNCHRONIZATION, WORKSHARING
	}

	/**
	 * Checks if this node already has its statement sub-node.
	 * 
	 * @return true iff the statement sub-node is not null.
	 */
	boolean isComplete();

	/**
	 * Returns the OpenMP statement kind of this node, i.e., either it is a
	 * parallel, worksharing or synchronization node.
	 * 
	 * @return the OpenMP statement kind of this node.
	 */
	OmpExecutableKind ompExecutableKind();

	/**
	 * Returns true iff nowait is applied.
	 * 
	 * @return true iff nowait is applied.
	 */
	boolean nowait();

	/**
	 * Updates the nowait flag.
	 * 
	 * @param value
	 *            The value to be used to update the nowait flag.
	 */
	void setNowait(boolean value);

	/**
	 * Returns the statement node affected by this OpenMP pragma. e.g., the
	 * following code is represented as an OpenMP parallel node with the
	 * following compound statements as its statement node.<br>
	 * <code>
	 * #prama omp parallel
	 * {
	 *   ...//statements
	 * }
	 * </code>
	 * 
	 * @return  the statement node affected by this OpenMP pragma.
	 */
	StatementNode statementNode();

	/**
	 * Updates the statement sub-node.
	 * 
	 * @param statementNode
	 *            The node to be used as the statement sub-node.
	 */
	void setStatementNode(StatementNode statementNode);

	/**
	 * Returns the list of identifier nodes declared by <code>shared</code>
	 * clause. There are several possibilities:
	 * <ul>
	 * <li><code>shared(x, y, z, ...)</code>: a non-empty sequence node;</li>
	 * <li><code>shared()</code>: an empty sequence node;</li>
	 * <li>no <code>shared</code> clause: null.</li>
	 * </ul>
	 * 
	 * @return the list of identifier nodes declared by <code>shared</code>
	 * clause.
	 */
	SequenceNode<IdentifierExpressionNode> sharedList();

	/**
	 * Updates the shared list of this node.
	 * 
	 * @param list
	 *            The list to be used as the shared list.
	 */
	void setSharedList(SequenceNode<IdentifierExpressionNode> list);

	/**
	 * Returns the list of identifier nodes declared by <code>private</code>
	 * clause. There are several possibilities:
	 * <ul>
	 * <li><code>private(x, y, z, ...)</code>: a non-empty sequence node;</li>
	 * <li><code>private()</code>: an empty sequence node;</li>
	 * <li>no <code>private</code> clause: null.</li>
	 * </ul>
	 * 
	 * @return the list of identifier nodes declared by <code>private</code>
	 * clause.
	 */
	SequenceNode<IdentifierExpressionNode> privateList();

	/**
	 * Updates the private list of this node.
	 * 
	 * @param list
	 *            The list to be used as the private list.
	 */
	void setPrivateList(SequenceNode<IdentifierExpressionNode> list);

	/**
	 * Returns the list of identifier nodes declared by
	 * <code>firstprivate</code> clause. There are several possibilities:
	 * <ul>
	 * <li><code>firstprivate(x, y, z, ...)</code>: a non-empty sequence node;</li>
	 * <li><code>firstprivate()</code>: an empty sequence node;</li>
	 * <li>no <code>firstprivate</code> clause: null.</li>
	 * </ul>
	 * 
	 * @return the list of identifier nodes declared by
	 * <code>firstprivate</code> clause.
	 */
	SequenceNode<IdentifierExpressionNode> firstprivateList();

	/**
	 * Updates the firstprivate list of this node.
	 * 
	 * @param list
	 *            The list to be used as the firstprivate list.
	 */
	void setFirstprivateList(SequenceNode<IdentifierExpressionNode> list);

	/**
	 * Returns the list of identifier nodes declared by <code>lastprivate</code>
	 * clause. There are several possibilities:
	 * <ul>
	 * <li><code>lastprivate(x, y, z, ...)</code>: a non-empty sequence node;</li>
	 * <li><code>lastprivate()</code>: an empty sequence node;</li>
	 * <li>no <code>lastprivate</code> clause: null.</li>
	 * </ul>
	 * 
	 * @return the list of identifier nodes declared by <code>lastprivate</code>
	 * clause.
	 */
	SequenceNode<IdentifierExpressionNode> lastprivateList();

	/**
	 * Updates the lastprivate list of this node.
	 * 
	 * @param list
	 *            The list to be used as the lastprivate list.
	 */
	void setLastprivateList(SequenceNode<IdentifierExpressionNode> list);

	/**
	 * Returns the list of identifier nodes declared by <code>copyin</code>
	 * clause. There are several possibilities:
	 * <ul>
	 * <li><code>copyin(x, y, z, ...)</code>: a non-empty sequence node;</li>
	 * <li><code>copyin()</code>: an empty sequence node;</li>
	 * <li>no <code>copyin</code> clause: null.</li>
	 * </ul>
	 * 
	 * @return
	 */
	SequenceNode<IdentifierExpressionNode> copyinList();

	/**
	 * Updates the copyin list of this node.
	 * 
	 * @param list
	 *            The list to be used as the copyin list.
	 */
	void setCopyinList(SequenceNode<IdentifierExpressionNode> list);

	/**
	 * Returns the list of identifier nodes declared by <code>copyprivate</code>
	 * clause. There are several possibilities:
	 * <ul>
	 * <li><code>copyprivate(x, y, z, ...)</code>: a non-empty sequence node;</li>
	 * <li><code>copyprivate()</code>: an empty sequence node;</li>
	 * <li>no <code>copyprivate</code> clause: null.</li>
	 * </ul>
	 * 
	 * @return the list of identifier nodes declared by <code>copyprivate</code>
	 * clause.
	 */
	SequenceNode<IdentifierExpressionNode> copyprivateList();

	/**
	 * Updates the copyprivate list of this node.
	 * 
	 * @param list
	 *            The list to be used as the copyprivate list.
	 */
	void setCopyprivateList(SequenceNode<IdentifierExpressionNode> list);

	/**
	 * Returns the list of identifier nodes declared by <code>reduction</code>
	 * clause.
	 * 
	 * There are several possibilities:
	 * <ul>
	 * <li><code>reduction(operator: x, y, z, ...)</code>: the operator and a
	 * non-empty sequence node;</li>
	 * <li>no <code>reduction</code> clause: null.</li>
	 * </ul>
	 * 
	 * @return the list of identifier nodes declared by <code>reduction</code>
	 * clause.
	 */
	SequenceNode<OmpReductionNode> reductionList();

	/**
	 * Updates the reduction list of this node.
	 * 
	 * @param list
	 *            The list to be used as the reduction list.
	 */
	void setReductionList(SequenceNode<OmpReductionNode> list);
}
