package edu.udel.cis.vsl.abc.ast.node.common.statement;

import java.io.PrintStream;

import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.StatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.WhenNode;
import edu.udel.cis.vsl.abc.token.IF.Source;

public class CommonWhenNode extends CommonStatementNode implements WhenNode {

	public CommonWhenNode(Source source, ExpressionNode guard,
			StatementNode body) {
		super(source, guard, body);
	}

	@Override
	public ExpressionNode getGuard() {
		return (ExpressionNode) child(0);
	}

	@Override
	public StatementNode getBody() {
		return (StatementNode) child(1);
	}

	@Override
	protected void printBody(PrintStream out) {
		out.print("When");
	}

	@Override
	public WhenNode copy() {
		ExpressionNode guard = getGuard();
		ExpressionNode guardCopy = guard == null ? null : guard.copy();
		StatementNode body = getBody();
		StatementNode bodyCopy = body == null ? null : body.copy();

		return new CommonWhenNode(getSource(), guardCopy, bodyCopy);
	}

	@Override
	public StatementKind statementKind() {
		return StatementKind.WHEN;
	}

}
