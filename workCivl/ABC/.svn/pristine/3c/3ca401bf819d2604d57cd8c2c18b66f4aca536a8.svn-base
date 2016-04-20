package edu.udel.cis.vsl.abc.ast.node.common.expression;

import java.io.PrintStream;

import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.StatementExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.CompoundStatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.ExpressionStatementNode;
import edu.udel.cis.vsl.abc.token.IF.Source;

public class CommonStatementExpressionNode extends CommonExpressionNode
		implements StatementExpressionNode {

	private ExpressionNode expression;

	public CommonStatementExpressionNode(Source source,
			CompoundStatementNode statement) {
		super(source, statement);
		assert statement.getSequenceChild(statement.numChildren() - 1) instanceof ExpressionStatementNode;
		expression = ((ExpressionStatementNode) statement
				.getSequenceChild(statement.numChildren() - 1)).getExpression();
	}

	@Override
	public ExpressionNode copy() {
		return new CommonStatementExpressionNode(this.getSource(), this
				.getCompoundStatement().copy());
	}

	@Override
	public ExpressionKind expressionKind() {
		return ExpressionKind.STATEMENT_EXPRESSION;
	}

	@Override
	public boolean isConstantExpression() {
		return false;
	}

	@Override
	public boolean isSideEffectFree(boolean errorsAreSideEffects) {
		return false;
	}

	@Override
	public CompoundStatementNode getCompoundStatement() {
		return (CompoundStatementNode) this.child(0);
	}

	@Override
	protected void printBody(PrintStream out) {
		out.print("StatementExpressionNode");
	}

	@Override
	public ExpressionNode getExpression() {
		return this.expression;
	}

}
