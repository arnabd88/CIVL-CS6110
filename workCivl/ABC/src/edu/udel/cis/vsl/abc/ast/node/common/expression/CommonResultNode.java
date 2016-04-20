package edu.udel.cis.vsl.abc.ast.node.common.expression;

import java.io.PrintStream;

import edu.udel.cis.vsl.abc.ast.node.IF.expression.ResultNode;
import edu.udel.cis.vsl.abc.token.IF.Source;

public class CommonResultNode extends CommonExpressionNode implements
		ResultNode {

	public CommonResultNode(Source source) {
		super(source);
	}

	@Override
	public boolean isConstantExpression() {
		return false;
	}

	@Override
	protected void printBody(PrintStream out) {
		out.print("$result");
	}

	@Override
	public ResultNode copy() {
		return new CommonResultNode(getSource());
	}

	@Override
	public ExpressionKind expressionKind() {
		return ExpressionKind.RESULT;
	}

	@Override
	public boolean isSideEffectFree(boolean errorsAreSideEffects) {
		return true;
	}
}
