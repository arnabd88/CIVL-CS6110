package edu.udel.cis.vsl.civl.model.IF.statement;

import java.util.ArrayList;

import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.LHSExpression;

/**
 * An MPI standard-mode blocking send statement. Syntax:
 * 
 * <pre>
 * int MPI_Send(const void* buf, int count, MPI_Datatype datatype,
 *              int dest, int tag, MPI_Comm comm)
 * </pre>
 * 
 * Note that there is a return value, which is used to return an error code.
 * Under normal circumstances it returns 0.
 * 
 * TODO: complete java-docs
 * 
 * @author siegel
 * 
 */
public interface MPISendStatement extends MPIStatement {

	/**
	 * Returns the send buffer argument.
	 * 
	 * @return the send buffer argument
	 */
	Expression getBuffer();

	/**
	 * Returns the send data size.
	 * 
	 * @return the send data size
	 */
	Expression getCount();

	/**
	 * Returns the send data type.
	 * 
	 * @return the send data type
	 */
	Expression getDatatype();

	/**
	 * Returns the target processor where the message send to.
	 * 
	 * @return the target processor where the message send to
	 */
	Expression getDestination();

	/**
	 * Returns the tag of the send message.
	 * 
	 * @return the tag of the send message
	 */
	Expression getTag();

	/**
	 * Returns the communicator of the processor.
	 * 
	 * @return the communicator of the processor
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

	/**
	 * Get arguments in the form of a expression list.
	 * 
	 * @return arguments list
	 */
	ArrayList<Expression> getArgumentsList();

}
