package edu.udel.cis.vsl.abc.ast.node.IF.statement;

import edu.udel.cis.vsl.abc.ast.node.IF.label.LabelNode;

public interface LabeledStatementNode extends StatementNode {

	LabelNode getLabel();

	StatementNode getStatement();

	@Override
	LabeledStatementNode copy();

}
