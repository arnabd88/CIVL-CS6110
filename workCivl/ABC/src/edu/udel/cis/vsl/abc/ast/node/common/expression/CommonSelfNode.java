package edu.udel.cis.vsl.abc.ast.node.common.expression;

import java.io.PrintStream;

import edu.udel.cis.vsl.abc.ast.node.IF.expression.SelfNode;
import edu.udel.cis.vsl.abc.ast.type.IF.ObjectType;
import edu.udel.cis.vsl.abc.token.IF.Source;

public class CommonSelfNode extends CommonConstantNode implements SelfNode {

	public CommonSelfNode(Source source, ObjectType processType) {
		super(source, "$self", processType);
	}

	@Override
	protected void printBody(PrintStream out) {
		out.print("$self");
	}

	@Override
	public ObjectType getInitialType() {
		return (ObjectType) super.getInitialType();
	}

	@Override
	public SelfNode copy() {
		return new CommonSelfNode(getSource(), getInitialType());
	}

	@Override
	public boolean isSideEffectFree(boolean errorsAreSideEffects) {
		return true;
	}

	@Override
	public ConstantKind constantKind() {
		return ConstantKind.SELF;
	}
}
