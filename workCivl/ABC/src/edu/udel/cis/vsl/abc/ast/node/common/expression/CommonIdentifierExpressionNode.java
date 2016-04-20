package edu.udel.cis.vsl.abc.ast.node.common.expression;

import java.io.PrintStream;

import edu.udel.cis.vsl.abc.ast.entity.IF.Entity;
import edu.udel.cis.vsl.abc.ast.entity.IF.Entity.EntityKind;
import edu.udel.cis.vsl.abc.ast.node.IF.IdentifierNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.IdentifierExpressionNode;
import edu.udel.cis.vsl.abc.token.IF.Source;

public class CommonIdentifierExpressionNode extends CommonExpressionNode
		implements IdentifierExpressionNode {

	public CommonIdentifierExpressionNode(Source source,
			IdentifierNode identifier) {
		super(source, identifier);
		assert identifier != null;
	}

	@Override
	public IdentifierNode getIdentifier() {
		return (IdentifierNode) child(0);
	}

	@Override
	public void setIdentifier(IdentifierNode identifier) {
		setChild(0, identifier);
	}

	@Override
	protected void printBody(PrintStream out) {
		out.print("IdentifierExpressionNode");
	}

	@Override
	public boolean isConstantExpression() {
		Entity entity = getIdentifier().getEntity();

		return entity.getEntityKind() == EntityKind.ENUMERATOR;
	}

	@Override
	public IdentifierExpressionNode copy() {
		return new CommonIdentifierExpressionNode(getSource(),
				duplicate(getIdentifier()));
	}

	@Override
	public ExpressionKind expressionKind() {
		return ExpressionKind.IDENTIFIER_EXPRESSION;
	}

	@Override
	public boolean isSideEffectFree(boolean errorsAreSideEffects) {
		return true;
	}
}
