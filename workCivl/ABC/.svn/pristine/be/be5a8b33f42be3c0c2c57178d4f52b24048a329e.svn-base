package edu.udel.cis.vsl.abc.ast.node.common.type;

import java.io.PrintStream;

import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.DomainTypeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.TypeNode;
import edu.udel.cis.vsl.abc.token.IF.Source;

public class CommonDomainTypeNode extends CommonTypeNode implements
		DomainTypeNode {

	public CommonDomainTypeNode(Source source, ExpressionNode dimension) {
		super(source, TypeNodeKind.DOMAIN, dimension);
	}

	@Override
	public TypeNode copy() {
		CommonDomainTypeNode result = new CommonDomainTypeNode(getSource(),
				duplicate(getDimension()));

		copyData(result);
		return result;
	}

	@Override
	public ExpressionNode getDimension() {
		return (ExpressionNode) child(0);
	}

	@Override
	protected void printBody(PrintStream out) {
		out.print("$domain");
	}

}
