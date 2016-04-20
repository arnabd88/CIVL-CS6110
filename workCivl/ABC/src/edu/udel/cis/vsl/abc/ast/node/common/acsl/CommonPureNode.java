package edu.udel.cis.vsl.abc.ast.node.common.acsl;

import java.io.PrintStream;

import edu.udel.cis.vsl.abc.ast.node.IF.acsl.ContractNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.PureNode;
import edu.udel.cis.vsl.abc.token.IF.Source;

public class CommonPureNode extends CommonContractNode implements PureNode {

	public CommonPureNode(Source source) {
		super(source, null);
	}

	@Override
	public ContractKind contractKind() {
		return ContractKind.PURE;
	}

	@Override
	public ContractNode copy() {
		return new CommonPureNode(this.getSource());
	}

	@Override
	protected void printBody(PrintStream out) {
		out.print("pure");
	}
}
