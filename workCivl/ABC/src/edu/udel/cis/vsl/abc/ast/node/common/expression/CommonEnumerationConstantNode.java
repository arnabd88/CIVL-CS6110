package edu.udel.cis.vsl.abc.ast.node.common.expression;

import java.io.PrintStream;

import edu.udel.cis.vsl.abc.ast.IF.DifferenceObject;
import edu.udel.cis.vsl.abc.ast.IF.DifferenceObject.DiffKind;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.IdentifierNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.EnumerationConstantNode;
import edu.udel.cis.vsl.abc.token.IF.Source;

public class CommonEnumerationConstantNode extends CommonExpressionNode
		implements EnumerationConstantNode {

	public CommonEnumerationConstantNode(Source source, IdentifierNode name) {
		super(source, name);
	}

	@Override
	public IdentifierNode getName() {
		return (IdentifierNode) child(0);
	}

	@Override
	public void setName(IdentifierNode name) {
		setChild(0, name);
	}

	@Override
	protected void printBody(PrintStream out) {
		out.print("EnumerationConstantNode");
	}

	@Override
	public EnumerationConstantNode copy() {
		return new CommonEnumerationConstantNode(getSource(),
				duplicate(getName()));
	}

	@Override
	public ConstantKind constantKind() {
		return ConstantKind.ENUM;
	}

	@Override
	public String getStringRepresentation() {
		return getName().name();
	}

	@Override
	public void setStringRepresentation(String representation) {
		getName().setName(representation);
	}

	@Override
	public ExpressionKind expressionKind() {
		return ExpressionKind.CONSTANT;
	}

	@Override
	public boolean isConstantExpression() {
		return true;
	}

	@Override
	public boolean isSideEffectFree(boolean errorsAreSideEffects) {
		return true;
	}

	@Override
	protected DifferenceObject diffWork(ASTNode that) {
		if (that instanceof EnumerationConstantNode)
			return null;
		else
			return new DifferenceObject(this, that, DiffKind.KIND);
	}
}
