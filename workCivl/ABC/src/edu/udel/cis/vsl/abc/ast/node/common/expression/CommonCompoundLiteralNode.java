package edu.udel.cis.vsl.abc.ast.node.common.expression;

import java.io.PrintStream;

import edu.udel.cis.vsl.abc.ast.node.IF.compound.CompoundInitializerNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.CompoundLiteralNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.TypeNode;
import edu.udel.cis.vsl.abc.token.IF.Source;

public class CommonCompoundLiteralNode extends CommonExpressionNode implements
		CompoundLiteralNode {

	public CommonCompoundLiteralNode(Source source, TypeNode typeNode,
			CompoundInitializerNode initializerList) {
		super(source, typeNode, initializerList);
	}

	@Override
	public boolean isConstantExpression() {
		return false;
	}

	@Override
	protected void printBody(PrintStream out) {
		out.print("CompoundLiteralNode");
	}

	@Override
	public TypeNode getTypeNode() {
		return (TypeNode) this.child(0);
	}

	@Override
	public CompoundInitializerNode getInitializerList() {
		return (CompoundInitializerNode) this.child(1);
	}

	@Override
	public CompoundLiteralNode copy() {
		return new CommonCompoundLiteralNode(getSource(),
				duplicate(getTypeNode()), duplicate(getInitializerList()));
	}

	@Override
	public ExpressionKind expressionKind() {
		return ExpressionKind.COMPOUND_LITERAL;
	}

	@Override
	public boolean isSideEffectFree(boolean errorsAreSideEffects) {
		return getInitializerList().isSideEffectFree(errorsAreSideEffects);
	}

	@Override
	public void setInitializerList(CompoundInitializerNode arg) {
		setChild(1, arg);
	}
}
