package edu.udel.cis.vsl.abc.ast.node.common.type;

import java.io.PrintStream;

import edu.udel.cis.vsl.abc.ast.node.IF.type.PointerTypeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.TypeNode;
import edu.udel.cis.vsl.abc.token.IF.Source;

public class CommonPointerTypeNode extends CommonTypeNode implements
		PointerTypeNode {

	public CommonPointerTypeNode(Source source, TypeNode baseType) {
		super(source, TypeNodeKind.POINTER, baseType);
	}

	@Override
	public TypeNode referencedType() {
		return (TypeNode) child(0);
	}

	@Override
	protected void printBody(PrintStream out) {
		String qualifiers = qualifierString();

		out.print("PointerType");
		if (!qualifiers.isEmpty())
			out.print("[" + qualifierString() + "]");
	}

	@Override
	public PointerTypeNode copy() {
		CommonPointerTypeNode result = new CommonPointerTypeNode(getSource(),
				duplicate(referencedType()));

		copyData(result);
		return result;
	}
}
