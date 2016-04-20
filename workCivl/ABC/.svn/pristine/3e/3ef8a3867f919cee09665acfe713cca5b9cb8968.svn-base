package edu.udel.cis.vsl.abc.ast.node.common.acsl;

import java.io.PrintStream;

import edu.udel.cis.vsl.abc.ast.node.IF.acsl.AnyactNode;
import edu.udel.cis.vsl.abc.token.IF.Source;

public class CommonAnyactNode extends CommonDependsEventNode implements
		AnyactNode {

	public CommonAnyactNode(Source source) {
		super(source);
	}

	@Override
	public DependsEventNodeKind getEventKind() {
		return DependsEventNodeKind.ANYACT;
	}

	@Override
	public AnyactNode copy() {
		return new CommonAnyactNode(getSource());
	}

	@Override
	protected void printBody(PrintStream out) {
		out.print("anyact");
	}

}
