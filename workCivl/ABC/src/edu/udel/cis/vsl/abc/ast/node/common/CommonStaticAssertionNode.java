package edu.udel.cis.vsl.abc.ast.node.common;

import java.io.PrintStream;

import edu.udel.cis.vsl.abc.ast.node.IF.StaticAssertionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.StringLiteralNode;
import edu.udel.cis.vsl.abc.token.IF.Source;

public class CommonStaticAssertionNode extends CommonASTNode implements
		StaticAssertionNode {

	public CommonStaticAssertionNode(Source source, ExpressionNode expression,
			StringLiteralNode message) {
		super(source, expression, message);
	}

	@Override
	public ExpressionNode getExpression() {
		return (ExpressionNode) child(0);
	}

	@Override
	public StringLiteralNode getMessage() {
		return (StringLiteralNode) child(1);
	}

	@Override
	protected void printBody(PrintStream out) {
		out.print("StaticAssertion");
	}

	@Override
	public StaticAssertionNode copy() {
		ExpressionNode expression = getExpression();
		ExpressionNode expressionCopy = expression == null ? null : expression
				.copy();
		StringLiteralNode message = getMessage();
		StringLiteralNode messageCopy = message == null ? null : message.copy();

		return new CommonStaticAssertionNode(getSource(), expressionCopy,
				messageCopy);
	}

	@Override
	public NodeKind nodeKind() {
		return NodeKind.STATIC_ASSERTION;
	}

	@Override
	public BlockItemKind blockItemKind() {
		// TODO Auto-generated method stub
		return BlockItemKind.STATIC_ASSERTION;
	}

}
