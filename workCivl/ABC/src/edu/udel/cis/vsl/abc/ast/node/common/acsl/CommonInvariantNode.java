package edu.udel.cis.vsl.abc.ast.node.common.acsl;

import java.io.PrintStream;

import edu.udel.cis.vsl.abc.ast.node.IF.acsl.InvariantNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.token.IF.Source;

public class CommonInvariantNode extends CommonContractNode implements
		InvariantNode {
	private boolean isLoopInvariant;

	public CommonInvariantNode(Source source, boolean isLoopInvariant,
			ExpressionNode expression) {
		super(source, expression);
		this.isLoopInvariant = isLoopInvariant;
	}

	@Override
	public ContractKind contractKind() {
		return ContractKind.INVARIANT;
	}

	@Override
	public ExpressionNode getExpression() {
		return (ExpressionNode) this.child(0);
	}

	@Override
	public InvariantNode copy() {
		return new CommonInvariantNode(this.getSource(), this.isLoopInvariant,
				duplicate(this.getExpression()));
	}

	@Override
	protected void printBody(PrintStream out) {
		if (isLoopInvariant)
			out.print("loop ");
		out.print("invariant");
	}

	@Override
	public boolean isLoopInvariant() {
		return this.isLoopInvariant;
	}
}
