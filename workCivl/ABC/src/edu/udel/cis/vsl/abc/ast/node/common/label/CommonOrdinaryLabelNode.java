package edu.udel.cis.vsl.abc.ast.node.common.label;

import java.io.PrintStream;

import edu.udel.cis.vsl.abc.ast.entity.IF.Function;
import edu.udel.cis.vsl.abc.ast.entity.IF.Label;
import edu.udel.cis.vsl.abc.ast.node.IF.IdentifierNode;
import edu.udel.cis.vsl.abc.ast.node.IF.label.OrdinaryLabelNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.StatementNode;
import edu.udel.cis.vsl.abc.ast.node.common.declaration.CommonDeclarationNode;
import edu.udel.cis.vsl.abc.token.IF.Source;

public class CommonOrdinaryLabelNode extends CommonDeclarationNode implements
		OrdinaryLabelNode {

	private Function function;

	private StatementNode statement;

	public CommonOrdinaryLabelNode(Source source, IdentifierNode name) {
		super(source, name);
	}

	@Override
	public Label getEntity() {
		return (Label) super.getEntity();
	}

	@Override
	public Function getFunction() {
		return function;
	}

	@Override
	public void setFunction(Function function) {
		this.function = function;
	}

	@Override
	public StatementNode getStatement() {
		return statement;
	}

	@Override
	public void setStatement(StatementNode statement) {
		this.statement = statement;
	}

	@Override
	protected void printBody(PrintStream out) {
		out.print("Label");
	}

	public String getName() {
		return getIdentifier().name();
	}

	@Override
	public OrdinaryLabelNode copy() {
		return new CommonOrdinaryLabelNode(getSource(),
				duplicate(getIdentifier()));
	}

	@Override
	public NodeKind nodeKind() {
		return NodeKind.ORDINARY_LABEL;
	}
}
