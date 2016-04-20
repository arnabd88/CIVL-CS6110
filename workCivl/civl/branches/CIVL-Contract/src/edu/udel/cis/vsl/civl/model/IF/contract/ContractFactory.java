package edu.udel.cis.vsl.civl.model.IF.contract;

import java.util.List;
import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.CIVLFunction;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.contract.CompositeEvent.CompositeEventOperator;
import edu.udel.cis.vsl.civl.model.IF.contract.MPICollectiveBehavior.MPICommunicationPattern;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;

/**
 * This factory is to create new instances of function contract components.
 * 
 * @author Manchun Zheng
 *
 */
public interface ContractFactory {
	/**
	 * Creates a new function behavior.
	 * 
	 * @param source
	 *            the source of the function behavior
	 * @return
	 */
	FunctionBehavior newFunctionBehavior(CIVLSource source);

	/**
	 * Creates a new named function behavior
	 * 
	 * @param source
	 * @param name
	 * @return
	 */
	NamedFunctionBehavior newNamedFunctionBehavior(CIVLSource source,
			String name);

	/**
	 * Creates a new function contract.
	 * 
	 * @param source
	 * @return
	 */
	FunctionContract newFunctionContract(CIVLSource source);

	/**
	 * Creates a new instance of call event.
	 * 
	 * @param function
	 * @param arguments
	 * @return
	 */
	CallEvent newCallEvent(CIVLSource source, CIVLFunction function,
			List<Expression> arguments);

	/**
	 * Creates a new instance of composite event.
	 * 
	 * @param source
	 * @param op
	 * @param left
	 * @param right
	 * @return
	 */
	CompositeEvent newCompositeEvent(CIVLSource source,
			CompositeEventOperator op, DependsEvent left, DependsEvent right);

	/**
	 * Creates a new instance of <code>\read</code> event.
	 * 
	 * @param source
	 * @param memoryUnits
	 * @return
	 */
	ReadOrWriteEvent newReadEvent(CIVLSource source, Set<Expression> memoryUnits);

	/**
	 * Creates a new instance of <code>\read</code> event.
	 * 
	 * @param source
	 * @param memoryUnits
	 * @return
	 */
	ReadOrWriteEvent newWriteEvent(CIVLSource source,
			Set<Expression> memoryUnits);

	/**
	 * Creates a new instance of <code>\anyact</code> event
	 * 
	 * @param source
	 * @return
	 */
	DependsEvent newAnyactEvent(CIVLSource source);

	/**
	 * Creates a new instance of <code>\noact</code> event
	 * 
	 * @param source
	 * @return
	 */
	DependsEvent newNoactEvent(CIVLSource source);

	/**
	 * Creates a new instance of <code>\mpi_collective(comm, pattern)</code>
	 * 
	 * @param source
	 * @param communicator
	 * @param pattern
	 * @return
	 */
	MPICollectiveBehavior newMPICollectiveBehavior(CIVLSource source,
			Expression communicator, MPICommunicationPattern pattern);

}
