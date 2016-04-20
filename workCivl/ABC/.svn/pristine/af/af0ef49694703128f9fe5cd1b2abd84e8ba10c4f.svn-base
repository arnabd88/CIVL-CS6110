package edu.udel.cis.vsl.abc.ast.node.common.acsl;

import java.io.PrintStream;

import edu.udel.cis.vsl.abc.ast.node.IF.acsl.RequiresNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.token.IF.Source;

public class CommonRequiresNode extends CommonContractNode implements
		RequiresNode {

	public CommonRequiresNode(Source source, ExpressionNode expression) {
		super(source, expression);
	}

	@Override
	public ExpressionNode getExpression() {
		return (ExpressionNode) child(0);
	}

	@Override
	protected void printBody(PrintStream out) {
		out.print("Requires");
	}

	@Override
	public RequiresNode copy() {
		return new CommonRequiresNode(getSource(), duplicate(getExpression()));
	}

	@Override
	public ContractKind contractKind() {
		return ContractKind.REQUIRES;
	}

}
