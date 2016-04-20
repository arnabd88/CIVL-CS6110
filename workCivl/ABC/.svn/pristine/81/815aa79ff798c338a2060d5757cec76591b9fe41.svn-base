package edu.udel.cis.vsl.abc.ast.node.common.expression;

import java.io.PrintStream;

import edu.udel.cis.vsl.abc.ast.node.IF.expression.ProcnullNode;
import edu.udel.cis.vsl.abc.ast.type.IF.ObjectType;
import edu.udel.cis.vsl.abc.token.IF.Source;

public class CommonProcnullNode extends CommonConstantNode implements
		ProcnullNode {
	public CommonProcnullNode(Source source, ObjectType processType) {
		super(source, "$proc_null", processType);
	}

	@Override
	protected void printBody(PrintStream out) {
		out.print("$proc_null");
	}

	@Override
	public ObjectType getInitialType() {
		return (ObjectType) super.getInitialType();
	}

	@Override
	public ProcnullNode copy() {
		return new CommonProcnullNode(getSource(), getInitialType());
	}

	@Override
	public boolean isSideEffectFree(boolean errorsAreSideEffects) {
		return true;
	}

	@Override
	public ConstantKind constantKind() {
		return ConstantKind.PROCNULL;
	}

}
