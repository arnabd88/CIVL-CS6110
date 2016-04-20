package edu.udel.cis.vsl.abc.ast.node.common.expression;

import java.io.PrintStream;

import edu.udel.cis.vsl.abc.ast.node.IF.expression.AlignOfNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.TypeNode;
import edu.udel.cis.vsl.abc.ast.type.IF.Type;
import edu.udel.cis.vsl.abc.token.IF.Source;

public class CommonAlignOfNode extends CommonExpressionNode implements
		AlignOfNode {

	public CommonAlignOfNode(Source source, TypeNode typeNode) {
		super(source, typeNode);
	}

	@Override
	public TypeNode getArgument() {
		return (TypeNode) child(0);
	}

	@Override
	public void setArgument(TypeNode typeNode) {
		setChild(0, typeNode);
	}

	@Override
	protected void printBody(PrintStream out) {
		out.print("AlignOfNode");
	}

	@Override
	public boolean isConstantExpression() {
		return !getArgument().getType().isVariablyModified();
	}

	public boolean equivalentConstant(ExpressionNode expression) {
		if (expression instanceof CommonAlignOfNode) {
			CommonAlignOfNode that = (CommonAlignOfNode) expression;
			Type thisType = getArgument().getType();
			Type thatType = that.getArgument().getType();

			return thisType.equals(thatType);
		}
		return false;
	}

	@Override
	public AlignOfNode copy() {
		return new CommonAlignOfNode(getSource(), duplicate(getArgument()));
	}

	@Override
	public ExpressionKind expressionKind() {
		return ExpressionKind.ALIGNOF;
	}
	
	@Override
	public boolean isSideEffectFree(boolean errorsAreSideEffects) {
		return true;
	}

}
