package edu.udel.cis.vsl.abc.ast.node.common.omp;

import java.io.PrintStream;

import edu.udel.cis.vsl.abc.ast.IF.DifferenceObject;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.IdentifierNode;
import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.IdentifierExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpSyncNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.StatementNode;
import edu.udel.cis.vsl.abc.err.IF.ABCRuntimeException;
import edu.udel.cis.vsl.abc.token.IF.Source;

public class CommonOmpSyncNode extends CommonOmpStatementNode implements
		OmpSyncNode {

	private OmpSyncNodeKind ompSyncNodeKind;

	/**
	 * Children
	 * <ul>
	 * <li>Children 0-7: same as {@link CommonOmpStatementNode};</li>
	 * <li>Child 8: SequenceNode&lt;IdentifierNode&gt; "flushedList", the list
	 * of identifiers declared by <code>flushed()</code> ;</li>
	 * <li>Child 9: IdentifierNode, optional "name" of critical construct.</li>
	 * </ul>
	 * 
	 * @param source
	 * @param identifier
	 * @param body
	 * @param eofToken
	 * @param kind
	 */
	public CommonOmpSyncNode(Source source, OmpSyncNodeKind kind,
			StatementNode statement) {
		super(source, statement);
		this.ompSyncNodeKind = kind;
		this.ompStatementKind = OmpExecutableKind.SYNCHRONIZATION;
		this.addChild(null);// child 8
		this.addChild(null);// child 9
	}

	@Override
	public boolean isComplete() {
		switch (this.ompSyncNodeKind) {
		case BARRIER:
		case FLUSH:
			return true;
		default:
			return super.isComplete();
		}
	}

	@Override
	public OmpSyncNodeKind ompSyncNodeKind() {
		return this.ompSyncNodeKind;
	}

	@Override
	public IdentifierNode criticalName() {
		return (IdentifierNode) this.child(9);
	}

	@SuppressWarnings("unchecked")
	@Override
	public SequenceNode<IdentifierExpressionNode> flushedList() {
		return (SequenceNode<IdentifierExpressionNode>) this.child(8);
	}

	// MASTER, CRITICAL, BARRIER, FLUSH
	@Override
	protected void printBody(PrintStream out) {
		switch (this.ompSyncNodeKind) {
		case MASTER:
			out.print("OmpMaster");
			break;
		case CRITICAL:
			out.print("OmpCritical");
			break;
		case BARRIER:
			out.print("OmpBarrier");
			break;
		case FLUSH:
			out.print("OmpFlush");
			break;
		case ORDERED:
			out.print("OmpOrdered");
			break;
		default:
			throw new ABCRuntimeException("Unreachable");
		}
	}

	@Override
	public void setCriticalName(IdentifierNode name) {
		assert this.ompSyncNodeKind == OmpSyncNodeKind.CRITICAL;
		this.setChild(9, name);
	}

	@Override
	public void setFlushedList(SequenceNode<IdentifierExpressionNode> list) {
		assert this.ompSyncNodeKind == OmpSyncNodeKind.FLUSH;
		this.setChild(8, list);
	}

	@Override
	public OmpSyncNode copy() {
		OmpSyncNode newSyncNode = new CommonOmpSyncNode(this.getSource(),
				this.ompSyncNodeKind, null);
		int numChildren = this.numChildren();

		for (int i = 0; i < numChildren; i++) {
			ASTNode child = this.child(i);

			if (child != null) {
				newSyncNode.setChild(i, child.copy());
			}
		}
		return newSyncNode;
	}

	@Override
	protected DifferenceObject diffWork(ASTNode that) {
		if (that instanceof OmpSyncNode)
			if (this.ompSyncNodeKind == ((OmpSyncNode) that).ompSyncNodeKind())
				return null;
		return new DifferenceObject(this, that);
	}
}
