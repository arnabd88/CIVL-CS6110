package edu.udel.cis.vsl.abc.ast.node.common.acsl;

import java.io.PrintStream;

import edu.udel.cis.vsl.abc.ast.node.IF.acsl.AssumesNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.token.IF.Source;

public class CommonAssumesNode extends CommonContractNode implements
		AssumesNode {

	public CommonAssumesNode(Source source, ExpressionNode predicate) {
		super(source, predicate);
	}

	@Override
	public ContractKind contractKind() {
		return ContractKind.ASSUMES;
	}

	@Override
	public ExpressionNode getPredicate() {
		return (ExpressionNode) this.child(0);
	}

	@Override
	public AssumesNode copy() {
		return new CommonAssumesNode(getSource(), duplicate(getPredicate()));
	}

	@Override
	protected void printBody(PrintStream out) {
		out.println("assumes");
	}

}
