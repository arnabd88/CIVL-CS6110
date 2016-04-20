package edu.udel.cis.vsl.abc.ast.node.common.type;

import java.io.PrintStream;

import edu.udel.cis.vsl.abc.ast.node.IF.IdentifierNode;
import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.TypedefNameNode;
import edu.udel.cis.vsl.abc.token.IF.Source;

public class CommonTypedefNameNode extends CommonTypeNode implements
		TypedefNameNode {

	public CommonTypedefNameNode(Source source, IdentifierNode name,
			SequenceNode<ExpressionNode> scopeList) {
		super(source, TypeNodeKind.TYPEDEF_NAME, name, scopeList);
	}

	@Override
	public IdentifierNode getName() {
		return (IdentifierNode) child(0);
	}

	@Override
	public void setName(IdentifierNode name) {
		setChild(0, name);
	}

	@Override
	protected void printBody(PrintStream out) {
		String qualifiers = qualifierString();

		out.print("TypedefName");
		if (!qualifiers.isEmpty())
			out.print("[" + qualifiers + "]");
	}

	@Override
	public TypedefNameNode copy() {
		CommonTypedefNameNode result = new CommonTypedefNameNode(getSource(),
				duplicate(getName()), duplicate(getScopeList()));

		result.copyData(result);
		return result;
	}

	@SuppressWarnings("unchecked")
	@Override
	public SequenceNode<ExpressionNode> getScopeList() {
		return (SequenceNode<ExpressionNode>) child(1);
	}

}
