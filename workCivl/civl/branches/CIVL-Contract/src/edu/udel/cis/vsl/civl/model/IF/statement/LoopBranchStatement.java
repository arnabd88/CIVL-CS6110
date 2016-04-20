package edu.udel.cis.vsl.civl.model.IF.statement;

public interface LoopBranchStatement extends NoopStatement {
	/**
	 * Is this the loop enter or exit statement?
	 * 
	 * @return True iff this is the loop enter branch.
	 */
	boolean isEnter();
}
