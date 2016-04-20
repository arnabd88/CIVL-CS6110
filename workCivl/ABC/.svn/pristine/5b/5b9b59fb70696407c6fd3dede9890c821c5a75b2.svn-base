package edu.udel.cis.vsl.abc.ast.node.IF.acsl;

import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;

public interface MPIContractExpressionNode extends ExpressionNode {
	public enum MPIContractExpressionKind {
		MPI_EMPTY_IN, MPI_EMPTY_OUT, MPI_EQUALS, MPI_REGION, MPI_AGREE, MPI_INTEGER_CONSTANT
	}

	MPIContractExpressionKind MPIContractExpressionKind();

	/**
	 * Return the number of arguments of this MPI expression
	 * 
	 * @return
	 */
	int numArguments();

	/**
	 * Returns the index-th argument
	 * 
	 * @param index
	 * @return
	 */
	ExpressionNode getArgument(int index);
}
