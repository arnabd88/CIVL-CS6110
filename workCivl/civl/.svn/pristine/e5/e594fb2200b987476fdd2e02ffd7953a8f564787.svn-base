package edu.udel.cis.vsl.civl.model.IF.statement;

import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.LHSExpression;

/**
 * An MPI_Barrier(which is used for block until all processes in the
 * communicator have reached this routine) statement. Syntax:
 * 
 * MPI_Barrier(MPI_Comm comm)
 * 
 * Note that there is a return value, which is used to return an error code.
 * Under normal circumstances it returns 0.
 * 
 * @author ziqingluo
 * 
 */
public interface MPIBarrierStatement extends Statement {

	/**
	 * Returns the communicator
	 * 
	 * @return
	 */
	Expression getCommunicator();

	/**
	 * Returns the left hand side, if the send statement occurs in an
	 * assignment. May be null.
	 * 
	 * @return left hand side of assignment or null
	 */
	LHSExpression getLeftHandSide();

	void setLeftHandSide(LHSExpression lhs);
}
