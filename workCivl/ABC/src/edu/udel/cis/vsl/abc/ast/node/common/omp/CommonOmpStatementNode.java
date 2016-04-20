package edu.udel.cis.vsl.abc.ast.node.common.omp;

import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.IdentifierExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpReductionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpExecutableNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.StatementNode;
import edu.udel.cis.vsl.abc.token.IF.Source;

@SuppressWarnings("unchecked")
public abstract class CommonOmpStatementNode extends CommonOmpNode implements
		OmpExecutableNode {

	/**
	 * The kind of this OpenMP Statement Node. It can be one of the following:
	 * PARALLEL, SYNCHRONIZATION, WORKSHARE.
	 */
	protected OmpExecutableKind ompStatementKind;

	/**
	 * True iff <code>nowait</code> clause is present.
	 */
	protected boolean nowait;

	/**
	 * 
	 * Children:
	 * <ul>
	 * <li>Child 0: SequenceNode&lt;IdentifierExpressionNode&gt; "sharedList",
	 * the list of identifiers declared by <code>shared</code></li>
	 * <li>Child 1: SequenceNode&lt;IdentifierExpressionNode&gt; "privateList",
	 * the list of identifiers declared by <code>private</code></li>
	 * <li>Child 2: SequenceNode&lt;IdentifierExpressionNode&gt;
	 * "firstprivateList", the list of identifiers declared by
	 * <code>firstprivate</code></li>
	 * <li>Child 3: SequenceNode&lt;IdentifierExpressionNode&gt;
	 * "lastprivateList", the list of identifiers declared by
	 * <code>lastprivate</code></li>
	 * <li>Child 4: SequenceNode&lt;IdentifierExpressionNode&gt; "copyinList",
	 * the list of identifiers declared by <code>copyin</code></li>
	 * <li>Child 5: SequenceNode&lt;IdentifierExpressionNode&gt;
	 * "copyprivateList", the list of identifiers declared by
	 * <code>copyprivate</code></li>
	 * <li>Child 6: SequenceNode&lt;OmpReductionNode&gt; "reductionList", the list
	 * of operators and identifiers declared by <code>reduction</code></li>
	 * <li>Child 7: StatementNode, the statement node affected by this pragma</li>
	 * </ul>
	 * 
	 * @param source
	 * @param identifier
	 * @param body
	 * @param eofToken
	 */
	public CommonOmpStatementNode(Source source, StatementNode statement) {
		super(source);
		nowait = false;
		this.addChild(null);// child 0
		this.addChild(null);// child 1
		this.addChild(null);// child 2
		this.addChild(null);// child 3
		this.addChild(null);// child 4
		this.addChild(null);// child 5
		this.addChild(null);// child 6
		this.addChild(statement);// child 7
	}

	@Override
	public boolean isComplete() {
		StatementNode statementNode = (StatementNode) this.child(7);

		if (statementNode != null) {
			if (statementNode instanceof OmpExecutableNode)
				return ((OmpExecutableNode) statementNode).isComplete();
			return true;
		} else
			return false;
	}

	@Override
	public boolean nowait() {
		return this.nowait;
	}

	@Override
	public void setNowait(boolean value) {
		this.nowait = value;
	}

	@Override
	public OmpNodeKind ompNodeKind() {
		return OmpNodeKind.EXECUTABLE;
	}

	@Override
	public StatementKind statementKind() {
		return StatementKind.OMP;
	}

	@Override
	public OmpExecutableKind ompExecutableKind() {
		return this.ompStatementKind;
	}

	@Override
	public StatementNode statementNode() {
		return (StatementNode) this.child(7);
	}

	@Override
	public void setStatementNode(StatementNode stmtNode) {
		this.setChild(7, stmtNode);
	}

	@Override
	public SequenceNode<IdentifierExpressionNode> sharedList() {
		return (SequenceNode<IdentifierExpressionNode>) this.child(0);
	}

	@Override
	public SequenceNode<IdentifierExpressionNode> privateList() {
		return (SequenceNode<IdentifierExpressionNode>) child(1);
	}

	@Override
	public SequenceNode<IdentifierExpressionNode> firstprivateList() {
		return (SequenceNode<IdentifierExpressionNode>) child(2);
	}

	@Override
	public SequenceNode<IdentifierExpressionNode> lastprivateList() {
		return (SequenceNode<IdentifierExpressionNode>) this.child(3);
	}

	@Override
	public SequenceNode<IdentifierExpressionNode> copyinList() {
		return (SequenceNode<IdentifierExpressionNode>) child(4);
	}

	@Override
	public SequenceNode<IdentifierExpressionNode> copyprivateList() {
		return (SequenceNode<IdentifierExpressionNode>) this.child(5);
	}

	@Override
	public SequenceNode<OmpReductionNode> reductionList() {
		return (SequenceNode<OmpReductionNode>) this.child(6);
	}

	@Override
	public void setSharedList(SequenceNode<IdentifierExpressionNode> list) {
		this.setChild(0, list);
	}

	@Override
	public void setPrivateList(SequenceNode<IdentifierExpressionNode> list) {
		this.setChild(1, list);
	}

	@Override
	public void setFirstprivateList(SequenceNode<IdentifierExpressionNode> list) {
		this.setChild(2, list);
	}

	@Override
	public void setLastprivateList(SequenceNode<IdentifierExpressionNode> list) {
		this.setChild(3, list);
	}

	@Override
	public void setCopyinList(SequenceNode<IdentifierExpressionNode> list) {
		this.setChild(4, list);
	}

	@Override
	public void setCopyprivateList(SequenceNode<IdentifierExpressionNode> list) {
		this.setChild(5, list);
	}

	@Override
	public void setReductionList(SequenceNode<OmpReductionNode> list) {
		this.setChild(6, list);
	}

	@Override
	public BlockItemKind blockItemKind() {
		return BlockItemKind.STATEMENT;
	}
}
