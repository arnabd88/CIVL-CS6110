package edu.udel.cis.vsl.abc.ast.node.common.acsl;

import java.io.PrintStream;

import edu.udel.cis.vsl.abc.ast.node.IF.acsl.EnsuresNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.token.IF.Source;

public class CommonEnsuresNode extends CommonContractNode implements
		EnsuresNode {

	public CommonEnsuresNode(Source source, ExpressionNode expression) {
		super(source, expression);
	}

	@Override
	public ExpressionNode getExpression() {
		return (ExpressionNode) child(0);
	}

	@Override
	protected void printBody(PrintStream out) {
		out.print("Ensures");
	}

	@Override
	public EnsuresNode copy() {
		return new CommonEnsuresNode(getSource(), duplicate(getExpression()));
	}

	@Override
	public ContractKind contractKind() {
		return ContractKind.ENSURES;
	}

}
