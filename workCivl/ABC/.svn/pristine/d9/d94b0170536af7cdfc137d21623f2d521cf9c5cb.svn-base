package edu.udel.cis.vsl.abc.ast.node.common.acsl;

import java.io.PrintStream;

import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.ContractNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.MPICollectiveBlockNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.token.IF.Source;

public class CommonMPICollectiveBlockNode extends CommonContractNode implements
		MPICollectiveBlockNode {
	private SequenceNode<ContractNode> body;

	private MPICollectiveKind kind;

	public CommonMPICollectiveBlockNode(Source source, ExpressionNode mpiComm,
			MPICollectiveKind kind, SequenceNode<ContractNode> body) {
		super(source, mpiComm, body);
		this.kind = kind;
		this.body = body;
	}

	@Override
	public ContractKind contractKind() {
		return ContractKind.MPI_COLLECTIVE;
	}

	@Override
	public ExpressionNode getMPIComm() {
		return (ExpressionNode) this.child(0);
	}

	@Override
	public MPICollectiveKind getCollectiveKind() {
		return kind;
	}

	@Override
	public SequenceNode<ContractNode> getBody() {
		return this.body;
	}

	@Override
	public MPICollectiveBlockNode copy() {
		return new CommonMPICollectiveBlockNode(this.getSource(),
				(ExpressionNode) child(0).copy(), kind, this.body);
	}

	@Override
	protected void printBody(PrintStream out) {
		out.print("\\mpi_collective");
	}
}
