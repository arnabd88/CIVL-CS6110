package edu.udel.cis.vsl.abc.ast.node.common.type;

import java.io.PrintStream;

import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.TypeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.TypeofNode;
import edu.udel.cis.vsl.abc.token.IF.Source;

public class CommonTypeofNode extends CommonTypeNode implements TypeofNode {

	public CommonTypeofNode(Source source, ExpressionNode expression) {
		super(source, TypeNodeKind.TYPEOF, expression);
	}

	public CommonTypeofNode(Source source, TypeNode type) {
		super(source, TypeNodeKind.TYPEOF, type);
	}

	@Override
	public TypeofNode copy() {
		if (this.hasExpressionOperand())
			return new CommonTypeofNode(this.getSource(), this
					.getExpressionOperand().copy());
		return new CommonTypeofNode(this.getSource(), this.getTypeOperand()
				.copy());
	}

	@Override
	protected void printBody(PrintStream out) {
		out.print("TypeofNode");
	}

	@Override
	public boolean hasExpressionOperand() {
		return (this.child(0) instanceof ExpressionNode);
	}

	@Override
	public ExpressionNode getExpressionOperand() {
		assert (this.child(0) instanceof ExpressionNode);
		return (ExpressionNode) this.child(0);
	}

	@Override
	public TypeNode getTypeOperand() {
		assert (this.child(0) instanceof TypeNode);
		return (TypeNode) this.child(0);
	}

}
