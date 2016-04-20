package edu.udel.cis.vsl.abc.ast.node.common.expression;

import java.io.PrintStream;

import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.IdentifierExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.RemoteExpressionNode;
import edu.udel.cis.vsl.abc.token.IF.Source;

public class CommonRemoteExpressionNode extends CommonExpressionNode implements
		RemoteExpressionNode {

	public CommonRemoteExpressionNode(Source source,
			ExpressionNode processExpression,
			IdentifierExpressionNode identifierNode) {
		super(source, processExpression, identifierNode);

	}

	@Override
	public boolean isConstantExpression() {
		return false;
	}

	@Override
	public ExpressionNode getProcessExpression() {
		return (ExpressionNode) child(0);
	}

	@Override
	public IdentifierExpressionNode getIdentifierNode() {
		return (IdentifierExpressionNode) child(1);
	}

	@Override
	protected void printBody(PrintStream out) {
		out.print("RemoteExpressionNode");
	}

	@Override
	public RemoteExpressionNode copy() {
		return new CommonRemoteExpressionNode(getSource(),
				duplicate(getProcessExpression()),
				duplicate(getIdentifierNode()));
	}

	@Override
	public ExpressionKind expressionKind() {
		return ExpressionKind.REMOTE_REFERENCE;
	}

	@Override
	public boolean isSideEffectFree(boolean errorsAreSideEffects) {
		return getProcessExpression().isSideEffectFree(errorsAreSideEffects);
	}

	@Override
	public void setProcessExpression(ExpressionNode arg) {
		setChild(0, arg);
	}

	@Override
	public void setIdentifierNode(IdentifierExpressionNode arg) {
		setChild(1, arg);
	}
}
