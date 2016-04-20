package edu.udel.cis.vsl.abc.ast.node.common.acsl;

import java.io.PrintStream;

import edu.udel.cis.vsl.abc.ast.node.IF.acsl.GuardsNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.token.IF.Source;

public class CommonGuardNode extends CommonContractNode implements GuardsNode {

	public CommonGuardNode(Source source, ExpressionNode expression) {
		super(source, expression);
	}

	@Override
	protected void printBody(PrintStream out) {
		out.print("guards");
	}

	@Override
	public GuardsNode copy() {
		return new CommonGuardNode(getSource(), duplicate(getExpression()));
	}

	@Override
	public ContractKind contractKind() {
		return ContractKind.GUARDS;
	}

	@Override
	public ExpressionNode getExpression() {
		return (ExpressionNode) child(0);
	}

}
