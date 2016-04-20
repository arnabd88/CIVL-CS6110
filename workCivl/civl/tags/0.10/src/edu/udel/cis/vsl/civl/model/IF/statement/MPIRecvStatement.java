package edu.udel.cis.vsl.civl.model.IF.statement;

import java.util.ArrayList;

import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.LHSExpression;

/**
 * An MPI standard-mode blocking receive statement. Syntax:
 * 
 * <pre>
 * int MPI_Recv(const void* buf, int count, MPI_Datatype datatype,
 *              int source, int tag, MPI_Comm comm, MPI_Status * status)
 * </pre>
 * 
 * TODO: complete java-docs
 * 
 * Note that there is a return value, which is used to return an error code.
 * Under normal circumstances it returns 0.
 * 
 * @author ziqingluo
 * 
 */
public interface MPIRecvStatement extends MPIStatement {

	/**
	 * Returns the receive buffer argument.
	 * 
	 * @return the receive buffer argument
	 */
	Expression getBuffer();

	/**
	 * Returns the received data size.
	 * 
	 * @return the received data size
	 */
	Expression getCount();

	/**
	 * Returns the received data type.
	 * 
	 * @return the received data type
	 */
	Expression getDatatype();

	/**
	 * Returns where is the received data come from or returns the wildcard
	 * "MPI_ANY_SOURCE".
	 * 
	 * @return where is the received data come from or "ANY_SOURCE"
	 */
	Expression getMPISource();

	/**
	 * Returns the tag of the received data.
	 * 
	 * @return the tag of the received data
	 */
	Expression getTag();

	/**
	 * Returns the communicator of the processor.
	 * 
	 * @return the communicator of the processor
	 */
	Expression getCommunicator();

	/**
	 * Returns the MPI_Status of the received message.
	 * 
	 * @return the MPI_Status of the received message
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

	/**
	 * Get arguments in the form of an expression list
	 * 
	 * @return the arguments list
	 */
	ArrayList<Expression> getArgumentsList();
}
