package edu.udel.cis.vsl.civl.model.IF.statement;

public interface MPIStatement extends Statement {
	public enum MPIStatementKind {
		IBARRIER, IRECV, ISEND, RECV, SEND, WAIT, OTHERS
	}
	
	MPIStatementKind mpiStatementKind();
}
