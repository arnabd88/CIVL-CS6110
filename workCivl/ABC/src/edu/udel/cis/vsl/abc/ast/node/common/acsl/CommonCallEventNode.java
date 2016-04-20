package edu.udel.cis.vsl.abc.ast.node.common.acsl;

import java.io.PrintStream;

import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.CallEventNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.IdentifierExpressionNode;
import edu.udel.cis.vsl.abc.token.IF.Source;

public class CommonCallEventNode extends CommonDependsEventNode implements
		CallEventNode {

	public CommonCallEventNode(Source source,
			IdentifierExpressionNode function,
			SequenceNode<ExpressionNode> arguments) {
		super(source, function, arguments);
	}

	@Override
	public DependsEventNodeKind getEventKind() {
		return DependsEventNodeKind.CALL;
	}

	@Override
	public CallEventNode copy() {
		return new CommonCallEventNode(getSource(), duplicate(getFunction()),
				duplicate(arguments()));
	}

	@Override
	public void printBody(PrintStream out) {
		out.print("\\call");
	}

	@Override
	public IdentifierExpressionNode getFunction() {
		return (IdentifierExpressionNode) this.child(0);
	}

	@SuppressWarnings("unchecked")
	@Override
	public SequenceNode<ExpressionNode> arguments() {
		return (SequenceNode<ExpressionNode>) this.child(1);
	}

}
