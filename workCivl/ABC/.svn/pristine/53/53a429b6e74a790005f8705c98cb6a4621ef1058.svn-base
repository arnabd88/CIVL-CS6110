package edu.udel.cis.vsl.abc.ast.node.common.acsl;

import java.io.PrintStream;

import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.MemoryEventNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.token.IF.Source;

public class CommonMemoryEventNode extends CommonDependsEventNode implements
		MemoryEventNode {

	private MemoryEventNodeKind kind;

	// private boolean isRead = true;// if false, then this is a write event

	public CommonMemoryEventNode(Source source, MemoryEventNodeKind kind,
			SequenceNode<ExpressionNode> memoryList) {
		super(source, memoryList);
		this.kind = kind;
	}

	@Override
	public DependsEventNodeKind getEventKind() {
		return DependsEventNodeKind.MEMORY;
	}

	@Override
	public MemoryEventNode copy() {
		return new CommonMemoryEventNode(this.getSource(), this.kind,
				duplicate(getMemoryList()));
	}

	@Override
	public boolean isRead() {
		return this.kind == MemoryEventNodeKind.READ;
	}

	@Override
	public boolean isWrite() {
		return this.kind == MemoryEventNodeKind.WRITE;
	}

	@SuppressWarnings("unchecked")
	@Override
	public SequenceNode<ExpressionNode> getMemoryList() {
		return (SequenceNode<ExpressionNode>) this.child(0);
	}

	@Override
	protected void printBody(PrintStream out) {
		switch (kind) {
		case READ:
			out.println("Read");
			break;
		case WRITE:
			out.println("Write");
			break;
		default:// REACH
			out.println("Reach");
		}
	}

	@Override
	public boolean isReach() {
		return this.kind == MemoryEventNodeKind.REACH;
	}

	@Override
	public MemoryEventNodeKind memoryEventKind() {
		return kind;
	}

}
