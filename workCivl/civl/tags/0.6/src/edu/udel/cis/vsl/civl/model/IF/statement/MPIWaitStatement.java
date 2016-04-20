package edu.udel.cis.vsl.civl.model.IF.statement;

import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.LHSExpression;

/**
 * A MPI wait statement. The MPI_Wait90 routine is used for waiting
 *  for a MPI request to complete. Syntax:
 *  
 * int MPI_Wait(MPI_Request *request, MPI_Status *status)
 *   
 * Note that there is a return value, which is used to return an error code.
 * Under normal circumstances it returns 0.
 * 
 * @author ziqingluo
 *
 */
public interface MPIWaitStatement extends Statement{
	/**
	 * Returns the communication request(handle).
	 * 
	 * @return The communication request(handle).
	 */
	Expression getRequest();
	
	/**
	 * Returns the status of the completed receive
	 * 
	 * @return the status of the completed receive
	 */
	Expression getStatus();
	
	/**
	 * Returns the left hand side, if the send statement occurs in an
	 * assignment. May be null.
	 * 
	 * @return left hand side of assignment or null
	 */
	LHSExpression getLeftHandSide();

	void setLeftHandSide(LHSExpression lhs);

}
