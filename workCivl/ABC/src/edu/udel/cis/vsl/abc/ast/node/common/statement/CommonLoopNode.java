package edu.udel.cis.vsl.abc.ast.node.common.statement;

import java.io.PrintStream;

import edu.udel.cis.vsl.abc.ast.IF.DifferenceObject;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.ContractNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.LoopNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.StatementNode;
import edu.udel.cis.vsl.abc.token.IF.Source;

public class CommonLoopNode extends CommonStatementNode implements LoopNode {

	private LoopKind loopKind;

	public CommonLoopNode(Source source, LoopKind loopKind,
			ExpressionNode condition, StatementNode body,
			SequenceNode<ContractNode> contracts) {
		super(source, condition, body, contracts);
		this.loopKind = loopKind;
	}

	@Override
	public ExpressionNode getCondition() {
		return (ExpressionNode) child(0);
	}

	@Override
	public StatementNode getBody() {
		return (StatementNode) child(1);
	}

	public ExpressionNode getInvariant() {
		return (ExpressionNode) child(2);
	}

	@Override
	public LoopKind getKind() {
		return loopKind;
	}

	@Override
	protected void printBody(PrintStream out) {
		switch (loopKind) {
		case WHILE:
			out.print("WhileLoopStatement");
			break;
		case DO_WHILE:
			out.print("DoWhileLoopStatement");
			break;
		case FOR:
			out.print("ForLoopStatement");
			break;
		default:
			throw new RuntimeException("Unreachable");
		}
	}

	@Override
	public LoopNode copy() {
		return new CommonLoopNode(getSource(), getKind(),
				duplicate(getCondition()), duplicate(getBody()),
				duplicate(loopContracts()));
	}

	@Override
	public StatementKind statementKind() {
		return StatementKind.LOOP;
	}

	@Override
	protected DifferenceObject diffWork(ASTNode that) {
		if (that instanceof LoopNode)
			if (this.loopKind == ((LoopNode) that).getKind())
				return null;
		return new DifferenceObject(this, that);
	}

	@Override
	public void setCondition(ExpressionNode condition) {
		setChild(0, condition);
	}

	@Override
	public void setBody(StatementNode body) {
		setChild(1, body);
	}

	@SuppressWarnings("unchecked")
	@Override
	public SequenceNode<ContractNode> loopContracts() {
		return (SequenceNode<ContractNode>) this.child(2);
	}

}
