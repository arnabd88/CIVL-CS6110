package edu.udel.cis.vsl.abc.ast.node.common.expression;

import java.io.PrintStream;

import edu.udel.cis.vsl.abc.ast.node.IF.IdentifierNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ArrowNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.token.IF.Source;

public class CommonArrowNode extends CommonExpressionNode implements ArrowNode {

	public CommonArrowNode(Source source, ExpressionNode structurePointer,
			IdentifierNode fieldName) {
		super(source, structurePointer, fieldName);
	}

	@Override
	public ExpressionNode getStructurePointer() {
		return (ExpressionNode) child(0);
	}

	@Override
	public void setStructurePointer(ExpressionNode structure) {
		setChild(0, structure);
	}

	@Override
	public IdentifierNode getFieldName() {
		return (IdentifierNode) child(1);
	}

	@Override
	public void setFieldName(IdentifierNode field) {
		setChild(1, field);
	}

	@Override
	protected void printBody(PrintStream out) {
		out.print("ArrowNode");
	}

	@Override
	public boolean isConstantExpression() {
		return false;
	}

	public boolean equivalentConstant(ExpressionNode expression) {
		return false;
	}

	@Override
	public ArrowNode copy() {
		return new CommonArrowNode(getSource(),
				duplicate(getStructurePointer()), duplicate(getFieldName()));
	}

	@Override
	public ExpressionKind expressionKind() {
		return ExpressionKind.ARROW;
	}

	@Override
	public boolean isSideEffectFree(boolean errorsAreSideEffects) {
		return !errorsAreSideEffects
				&& getStructurePointer().isSideEffectFree(errorsAreSideEffects);
	}

}
