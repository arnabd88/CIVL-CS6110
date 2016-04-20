package edu.udel.cis.vsl.abc.analysis.entity;

import edu.udel.cis.vsl.abc.ast.node.IF.compound.ScalarLiteralObject;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;

public class CommonScalarLiteralObject extends CommonLiteralObject implements
		ScalarLiteralObject {

	private ExpressionNode expression;

	public CommonScalarLiteralObject(LiteralTypeNode typeNode,
			ExpressionNode expression) {
		super(typeNode, expression);
		this.expression = expression;
	}

	@Override
	public ExpressionNode getExpression() {
		return expression;
	}

	@Override
	public String toString() {
		return expression.toString();
	}

}
