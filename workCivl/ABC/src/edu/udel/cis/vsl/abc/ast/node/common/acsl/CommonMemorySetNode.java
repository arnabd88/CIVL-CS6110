package edu.udel.cis.vsl.abc.ast.node.common.acsl;

import java.io.PrintStream;

import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.MemorySetNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.VariableDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.common.expression.CommonExpressionNode;
import edu.udel.cis.vsl.abc.token.IF.Source;

public class CommonMemorySetNode extends CommonExpressionNode implements
		MemorySetNode {

	public CommonMemorySetNode(Source source, ExpressionNode elements,
			SequenceNode<VariableDeclarationNode> binders,
			ExpressionNode predicate) {
		super(source, elements, binders, predicate);
	}

	@Override
	public MemorySetNode copy() {
		return new CommonMemorySetNode(this.getSource(),
				duplicate(this.getElements()), duplicate(this.getBinders()),
				duplicate(this.getPredicate()));
	}

	@Override
	public ExpressionKind expressionKind() {
		return ExpressionKind.MEMORY_SET;
	}

	@Override
	public boolean isConstantExpression() {
		return false;
	}

	@Override
	public boolean isSideEffectFree(boolean errorsAreSideEffects) {
		return true;
	}

	@Override
	public ExpressionNode getElements() {
		return (ExpressionNode) this.child(0);
	}

	@SuppressWarnings("unchecked")
	@Override
	public SequenceNode<VariableDeclarationNode> getBinders() {
		return (SequenceNode<VariableDeclarationNode>) this.child(1);
	}

	@Override
	public ExpressionNode getPredicate() {
		return (ExpressionNode) this.child(2);
	}

	@Override
	protected void printBody(PrintStream out) {
		out.print("memory set");
	}

}
