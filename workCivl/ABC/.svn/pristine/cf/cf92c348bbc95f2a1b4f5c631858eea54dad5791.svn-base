package edu.udel.cis.vsl.abc.ast.node.common.compound;

import java.io.PrintStream;

import edu.udel.cis.vsl.abc.ast.node.IF.IdentifierNode;
import edu.udel.cis.vsl.abc.ast.node.IF.compound.FieldDesignatorNode;
import edu.udel.cis.vsl.abc.ast.node.common.CommonASTNode;
import edu.udel.cis.vsl.abc.token.IF.Source;

public class CommonFieldDesignatorNode extends CommonASTNode implements
		FieldDesignatorNode {

	public CommonFieldDesignatorNode(Source source, IdentifierNode field) {
		super(source, field);
	}

	@Override
	public IdentifierNode getField() {
		return (IdentifierNode) child(0);
	}

	@Override
	public void setField(IdentifierNode name) {
		setChild(0, name);
	}

	@Override
	protected void printBody(PrintStream out) {
		out.print("Field");
	}

	@Override
	public FieldDesignatorNode copy() {
		return new CommonFieldDesignatorNode(getSource(), duplicate(getField()));
	}

	@Override
	public NodeKind nodeKind() {
		return NodeKind.FIELD_DESIGNATOR;
	}

}
