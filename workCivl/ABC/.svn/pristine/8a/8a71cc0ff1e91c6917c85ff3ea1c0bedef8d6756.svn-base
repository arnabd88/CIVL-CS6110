package edu.udel.cis.vsl.abc.ast.node.common.expression;

import java.io.PrintStream;

import edu.udel.cis.vsl.abc.ast.node.IF.expression.WildcardNode;
import edu.udel.cis.vsl.abc.token.IF.Source;

public class CommonWildcardNode extends CommonExpressionNode implements
		WildcardNode {

	public CommonWildcardNode(Source source) {
		super(source);
	}

	@Override
	public WildcardNode copy() {
		return new CommonWildcardNode(this.getSource());
	}

	@Override
	protected void printBody(PrintStream out) {
		out.print("...");
	}

	@Override
	public ExpressionKind expressionKind() {
		return ExpressionKind.WILDCARD;
	}

	@Override
	public boolean isConstantExpression() {
		return true;
	}

	@Override
	public boolean isSideEffectFree(boolean errorsAreSideEffects) {
		return true;
	}

}
