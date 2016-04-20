package edu.udel.cis.vsl.abc.ast.node.common.statement;

import java.io.PrintStream;

import edu.udel.cis.vsl.abc.ast.node.IF.statement.NullStatementNode;
import edu.udel.cis.vsl.abc.token.IF.Source;

public class CommonNullStatementNode extends CommonStatementNode implements
		NullStatementNode {

	public CommonNullStatementNode(Source source) {
		super(source);
	}

	@Override
	protected void printBody(PrintStream out) {
		out.print("NullStatement");
	}

	@Override
	public NullStatementNode copy() {
		return new CommonNullStatementNode(getSource());
	}

	@Override
	public StatementKind statementKind() {
		return StatementKind.NULL;
	}
}
