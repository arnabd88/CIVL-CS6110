package edu.udel.cis.vsl.abc.ast.node.common.expression;

import java.io.PrintStream;

import edu.udel.cis.vsl.abc.ast.node.IF.expression.CastNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.TypeNode;
import edu.udel.cis.vsl.abc.token.IF.Source;

public class CommonCastNode extends CommonExpressionNode implements CastNode {

	public CommonCastNode(Source source, TypeNode typeNode,
			ExpressionNode expression) {
		super(source, typeNode, expression);
	}

	@Override
	public TypeNode getCastType() {
		return (TypeNode) child(0);
	}

	@Override
	public ExpressionNode getArgument() {
		return (ExpressionNode) child(1);
	}

	@Override
	public void setCastType(TypeNode typeNode) {
		setChild(0, typeNode);
	}

	@Override
	public void setArgument(ExpressionNode expression) {
		setChild(1, expression);
	}

	@Override
	protected void printBody(PrintStream out) {
		out.print("CastNode");
	}

	@Override
	public boolean isConstantExpression() {
		return !getCastType().getType().isVariablyModified()
				&& getArgument().isConstantExpression();
	}

	@Override
	public CastNode copy() {
		return new CommonCastNode(getSource(), duplicate(getCastType()),
				duplicate(getArgument()));
	}

	@Override
	public ExpressionKind expressionKind() {
		return ExpressionKind.CAST;
	}

	@Override
	public boolean isSideEffectFree(boolean errorsAreSideEffects) {
		return getArgument().isSideEffectFree(errorsAreSideEffects);
	}

}
