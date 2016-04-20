package edu.udel.cis.vsl.abc.ast.node.common.expression;

import java.io.PrintStream;

import edu.udel.cis.vsl.abc.ast.node.IF.PairNode;
import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.DerivativeExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.IdentifierExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.IntegerConstantNode;
import edu.udel.cis.vsl.abc.token.IF.Source;

public class CommonDerivativeExpressionNode extends CommonExpressionNode
		implements DerivativeExpressionNode {

	// private ExpressionNode function;
	//
	// private SequenceNode<PairNode<IdentifierExpressionNode,
	// IntegerConstantNode>> partials;
	//
	// private SequenceNode<ExpressionNode> arguments;

	public CommonDerivativeExpressionNode(
			Source source,
			ExpressionNode function,
			SequenceNode<PairNode<IdentifierExpressionNode, IntegerConstantNode>> partials,
			SequenceNode<ExpressionNode> arguments) {
		super(source, function, partials, arguments);
		// this.function = function;
		// this.partials = partials;
		// this.arguments = arguments;
	}

	@Override
	public boolean isConstantExpression() {
		return false;
	}

	@Override
	public ExpressionKind expressionKind() {
		return ExpressionKind.DERIVATIVE_EXPRESSION;
	}

	@Override
	public ExpressionNode getFunction() {
		return (ExpressionNode) this.child(0);
	}

	@Override
	public int getNumberOfArguments() {
		return this.child(2).numChildren();
	}

	@SuppressWarnings("unchecked")
	@Override
	public ExpressionNode getArgument(int index) {
		return ((SequenceNode<ExpressionNode>) this.child(2))
				.getSequenceChild(index);
	}

	@Override
	public int getNumberOfPartials() {
		return this.child(1).numChildren();
	}

	@SuppressWarnings("unchecked")
	@Override
	public PairNode<IdentifierExpressionNode, IntegerConstantNode> getPartial(
			int index) {
		return ((SequenceNode<PairNode<IdentifierExpressionNode, IntegerConstantNode>>) this
				.child(1)).getSequenceChild(index);
	}

	@SuppressWarnings("unchecked")
	@Override
	public DerivativeExpressionNode copy() {
		return new CommonDerivativeExpressionNode(
				getSource(),
				duplicate(this.getFunction()),
				(SequenceNode<PairNode<IdentifierExpressionNode, IntegerConstantNode>>) duplicate(this
						.child(1)),
				(SequenceNode<ExpressionNode>) duplicate(this.child(2)));
	}

	@Override
	protected void printBody(PrintStream out) {
		out.print("DerivativeExpressionNode");
	}

	@Override
	public boolean isSideEffectFree(boolean errorsAreSideEffects) {
		boolean result = true;

		for (int i = 0; i < getNumberOfArguments(); i++) {
			result = result
					&& getArgument(i).isSideEffectFree(errorsAreSideEffects);
		}
		return true;
	}
}
