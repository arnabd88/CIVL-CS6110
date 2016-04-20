package edu.udel.cis.vsl.abc.ast.node.common.expression;

import java.io.PrintStream;

import edu.udel.cis.vsl.abc.ast.node.IF.expression.CallsNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.FunctionCallNode;
import edu.udel.cis.vsl.abc.token.IF.Source;

public class CommonCallsNode extends CommonExpressionNode implements CallsNode {

	public CommonCallsNode(Source source, FunctionCallNode callNode) {
		super(source, callNode);
	}

	@Override
	public boolean isConstantExpression() {
		return false;
	}

	@Override
	public FunctionCallNode getCall() {
		return (FunctionCallNode) child(0);
	}

	@Override
	protected void printBody(PrintStream out) {
		out.print("CallsNode");
	}

	@Override
	public CallsNode copy() {
		return new CommonCallsNode(getSource(), duplicate(getCall()));
	}

	@Override
	public ExpressionKind expressionKind() {
		return ExpressionKind.CALLS;
	}

	@Override
	public boolean isSideEffectFree(boolean errorsAreSideEffects) {
		return false;
	}

	@Override
	public void setCall(FunctionCallNode call) {
		this.setChild(0, call);
	}

}
