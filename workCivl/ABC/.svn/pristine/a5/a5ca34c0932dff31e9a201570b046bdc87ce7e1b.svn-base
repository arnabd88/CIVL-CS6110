package edu.udel.cis.vsl.abc.ast.node.common.statement;

import java.io.PrintStream;

import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.IfNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.StatementNode;
import edu.udel.cis.vsl.abc.token.IF.Source;

public class CommonIfNode extends CommonStatementNode implements IfNode {

	public CommonIfNode(Source source, ExpressionNode condition,
			StatementNode trueBranch) {
		super(source, condition, trueBranch);
	}

	public CommonIfNode(Source source, ExpressionNode condition,
			StatementNode trueBranch, StatementNode falseBranch) {
		super(source, condition, trueBranch, falseBranch);
	}

	@Override
	public ExpressionNode getCondition() {
		return (ExpressionNode) child(0);
	}

	@Override
	public StatementNode getTrueBranch() {
		return (StatementNode) child(1);
	}

	@Override
	public StatementNode getFalseBranch() {
		if (numChildren() < 3)
			return null;
		else
			return (StatementNode) child(2);
	}

	@Override
	protected void printBody(PrintStream out) {
		out.print("IfStatement");
	}

	@Override
	public IfNode copy() {
		StatementNode falseBranch = getFalseBranch();

		if (falseBranch == null)
			return new CommonIfNode(getSource(), duplicate(getCondition()),
					duplicate(getTrueBranch()));
		else
			return new CommonIfNode(getSource(), duplicate(getCondition()),
					duplicate(getTrueBranch()), duplicate(falseBranch));
	}

	@Override
	public StatementKind statementKind() {
		return StatementKind.IF;
	}
}
