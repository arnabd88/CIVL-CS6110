package edu.udel.cis.vsl.civl.model.IF.expression;

public interface MPIContractExpression extends Expression {
	static public enum MPI_CONTRACT_EXPRESSION_KIND {
		MPI_EMPTY_IN, MPI_EMPTY_OUT, MPI_SIZE, MPI_EQUALS, MPI_REGION
	}

	MPI_CONTRACT_EXPRESSION_KIND mpiContractKind();

	Expression communicator();

	Expression[] arguments();
}
