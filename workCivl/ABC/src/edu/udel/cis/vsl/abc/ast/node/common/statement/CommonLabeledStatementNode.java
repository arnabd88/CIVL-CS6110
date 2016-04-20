package edu.udel.cis.vsl.abc.ast.node.common.statement;

import java.io.PrintStream;

import edu.udel.cis.vsl.abc.ast.node.IF.label.LabelNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.LabeledStatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.StatementNode;
import edu.udel.cis.vsl.abc.token.IF.Source;

public class CommonLabeledStatementNode extends CommonStatementNode implements
		LabeledStatementNode {

	public CommonLabeledStatementNode(Source source, LabelNode label,
			StatementNode statement) {
		super(source, label, statement);
	}

	@Override
	public LabelNode getLabel() {
		return (LabelNode) child(0);
	}

	@Override
	public StatementNode getStatement() {
		return (StatementNode) child(1);
	}

	@Override
	protected void printBody(PrintStream out) {
		out.print("LabeledStatement");
	}

	@Override
	public LabeledStatementNode copy() {
		return new CommonLabeledStatementNode(getSource(),
				duplicate(getLabel()), duplicate(getStatement()));
	}

	@Override
	public StatementKind statementKind() {
		return StatementKind.LABELED;
	}
}
