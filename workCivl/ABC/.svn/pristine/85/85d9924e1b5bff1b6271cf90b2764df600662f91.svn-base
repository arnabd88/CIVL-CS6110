package edu.udel.cis.vsl.abc.ast.node.common.expression;

import java.io.PrintStream;

import edu.udel.cis.vsl.abc.ast.node.IF.IdentifierNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.DotNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.token.IF.Source;

public class CommonDotNode extends CommonExpressionNode implements DotNode {

	public CommonDotNode(Source source, ExpressionNode structure,
			IdentifierNode fieldName) {
		super(source, structure, fieldName);
	}

	@Override
	public ExpressionNode getStructure() {
		return (ExpressionNode) child(0);
	}

	@Override
	public void setStructure(ExpressionNode structure) {
		setChild(0, structure);
	}

	@Override
	public IdentifierNode getFieldName() {
		return (IdentifierNode) child(1);
	}

	@Override
	public void setFieldName(IdentifierNode field) {
		setChild(1, field);
	}

	@Override
	protected void printBody(PrintStream out) {
		out.print("DotNode");
	}

	@Override
	public boolean isConstantExpression() {
		return false;
	}

	@Override
	public DotNode copy() {
		return new CommonDotNode(getSource(), duplicate(getStructure()),
				duplicate(getFieldName()));
	}

	@Override
	public ExpressionKind expressionKind() {
		return ExpressionKind.DOT;
	}
	
	@Override
	public boolean isSideEffectFree(boolean errorsAreSideEffects) {
		return getStructure().isSideEffectFree(errorsAreSideEffects);
	}
}
