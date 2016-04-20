package edu.udel.cis.vsl.abc.ast.node.common.acsl;

import java.io.PrintStream;
import java.util.Arrays;

import edu.udel.cis.vsl.abc.ast.node.IF.acsl.MPIContractConstantNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.token.IF.Source;

public class CommonMPIConstantNode extends CommonMPIContractExpressionNode
		implements MPIContractConstantNode {

	private MPIConstantKind kind;

	private ConstantKind constKind;

	private String stringReresentation;

	public CommonMPIConstantNode(Source source, String name,
			MPIConstantKind kind, ConstantKind constKind) {
		super(source, Arrays.asList((ExpressionNode) null),
				MPIContractExpressionKind.MPI_INTEGER_CONSTANT, name);
		this.kind = kind;
		this.constKind = constKind;
	}

	@Override
	public MPIConstantKind getMPIConstantKind() {
		return kind;
	}

	@Override
	public MPIContractConstantNode copy() {
		return new CommonMPIConstantNode(this.getSource(), this
				.getStringRepresentation().toString(), kind, constKind);
	}

	@Override
	protected void printBody(PrintStream out) {
		out.print(kind);
	}

	@Override
	public ConstantKind constantKind() {
		return constKind;
	}

	@Override
	public String getStringRepresentation() {
		return this.stringReresentation;
	}

	@Override
	public void setStringRepresentation(String representation) {
		this.stringReresentation = representation;
	}
}
