package edu.udel.cis.vsl.abc.ast.node.common.acsl;

import java.io.PrintStream;

import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.AssignsOrReadsNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.token.IF.Source;

public class CommonAssignsOrReadsNode extends CommonContractNode implements
		AssignsOrReadsNode {

	private boolean isAssigns;

	public CommonAssignsOrReadsNode(Source source, boolean isAssigns,
			SequenceNode<ExpressionNode> child) {
		super(source, (ASTNode) child);
		this.isAssigns = isAssigns;
	}

	@Override
	public ContractKind contractKind() {
		return ContractKind.ASSIGNS_READS;
	}

	@SuppressWarnings("unchecked")
	@Override
	public SequenceNode<ExpressionNode> getMemoryList() {
		return (SequenceNode<ExpressionNode>) this.child(0);
	}

	@Override
	public AssignsOrReadsNode copy() {
		return new CommonAssignsOrReadsNode(this.getSource(), this.isAssigns,
				duplicate(getMemoryList()));
	}

	@Override
	protected void printBody(PrintStream out) {
		if (this.isAssigns)
			out.print("Assigns");
		else
			out.print("Reads");
	}

	@Override
	public boolean isAssigns() {
		return this.isAssigns;
	}

	@Override
	public boolean isReads() {
		return !this.isAssigns;
	}

}
