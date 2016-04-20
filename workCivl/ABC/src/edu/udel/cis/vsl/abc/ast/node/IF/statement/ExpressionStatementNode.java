package edu.udel.cis.vsl.abc.ast.node.IF.statement;

import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;

public interface ExpressionStatementNode extends StatementNode {

	ExpressionNode getExpression();

	@Override
	ExpressionStatementNode copy();
}
