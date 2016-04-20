package edu.udel.cis.vsl.abc.ast.node.common.statement;

import java.io.PrintStream;

import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.ExpressionStatementNode;
import edu.udel.cis.vsl.abc.token.IF.Source;

public class CommonExpressionStatementNode extends CommonStatementNode
		implements ExpressionStatementNode {

	public CommonExpressionStatementNode(Source source,
			ExpressionNode expression) {
		super(source, expression);
//		assert expression != null;
	}

	@Override
	public ExpressionNode getExpression() {
		return (ExpressionNode) child(0);
	}

	@Override
	protected void printBody(PrintStream out) {
		out.print("ExpressionStatement");
	}

	@Override
	public ExpressionStatementNode copy() {
		return new CommonExpressionStatementNode(getSource(),
				duplicate(getExpression()));
	}

	@Override
	public StatementKind statementKind() {
		return StatementKind.EXPRESSION;
	}

}
