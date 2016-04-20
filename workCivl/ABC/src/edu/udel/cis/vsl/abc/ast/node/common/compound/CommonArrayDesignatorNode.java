package edu.udel.cis.vsl.abc.ast.node.common.compound;

import java.io.PrintStream;

import edu.udel.cis.vsl.abc.ast.node.IF.compound.ArrayDesignatorNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.common.CommonASTNode;
import edu.udel.cis.vsl.abc.token.IF.Source;

public class CommonArrayDesignatorNode extends CommonASTNode implements
		ArrayDesignatorNode {

	public CommonArrayDesignatorNode(Source source, ExpressionNode index) {
		super(source, index);
	}

	@Override
	public ExpressionNode getIndex() {
		return (ExpressionNode) child(0);
	}

	@Override
	public void setIndex(ExpressionNode expression) {
		setChild(0, expression);
	}

	@Override
	protected void printBody(PrintStream out) {
		out.print("ArrayIndex");
	}

	@Override
	public ArrayDesignatorNode copy() {
		return new CommonArrayDesignatorNode(getSource(), duplicate(getIndex()));
	}

	@Override
	public NodeKind nodeKind() {
		return NodeKind.ARRAY_DESIGNATOR;
	}

}
