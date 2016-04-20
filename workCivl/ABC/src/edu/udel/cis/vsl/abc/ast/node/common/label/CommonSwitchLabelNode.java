package edu.udel.cis.vsl.abc.ast.node.common.label;

import java.io.PrintStream;

import edu.udel.cis.vsl.abc.ast.IF.DifferenceObject;
import edu.udel.cis.vsl.abc.ast.IF.DifferenceObject.DiffKind;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.label.SwitchLabelNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.StatementNode;
import edu.udel.cis.vsl.abc.ast.node.common.CommonASTNode;
import edu.udel.cis.vsl.abc.token.IF.Source;

public class CommonSwitchLabelNode extends CommonASTNode implements
		SwitchLabelNode {

	private boolean isDefault;

	private StatementNode statement = null;

	public CommonSwitchLabelNode(Source source, ExpressionNode caseExpression) {
		super(source, caseExpression);
		isDefault = false;
	}

	public CommonSwitchLabelNode(Source source) {
		super(source);
		isDefault = true;
	}

	@Override
	public boolean isDefault() {
		return isDefault;
	}

	@Override
	public ExpressionNode getExpression() {
		return (ExpressionNode) child(0);
	}

	@Override
	protected void printBody(PrintStream out) {
		if (isDefault)
			out.print("Default");
		else
			out.print("Case");
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
	public SwitchLabelNode copy() {
		if (isDefault) {
			return new CommonSwitchLabelNode(getSource());
		}
		return new CommonSwitchLabelNode(getSource(),
				duplicate(getExpression()));
	}

	@Override
	public NodeKind nodeKind() {
		return NodeKind.SWITCH_LABEL;
	}

	@Override
	protected DifferenceObject diffWork(ASTNode that) {
		if (that instanceof SwitchLabelNode) {
			SwitchLabelNode thatSwitch = (SwitchLabelNode) that;

			if (this.isDefault == thatSwitch.isDefault())
				return null;
			else
				return new DifferenceObject(this, that, DiffKind.OTHER,
						"different case/default lable");
		}
		return new DifferenceObject(this, that);
	}
}
