package edu.udel.cis.vsl.civl.model.IF.contract;

import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.expression.Expression;

/**
 * This represents a <code>\read</code> or <code>\write</code> event of a
 * <code>depends</code> clause.
 * 
 * @author Manchun Zheng
 *
 */
public interface ReadOrWriteEvent extends DependsEvent {
	/**
	 * Returns the memory units associated with this event.
	 * 
	 * @return
	 */
	Set<Expression> memoryUnits();

	/**
	 * Returns the number of memory units associated with this event.
	 * 
	 * @return
	 */
	int numMemoryUnits();

	/**
	 * Is this a <code>\read</code> event?
	 * 
	 * @return
	 */
	boolean isRead();

	/**
	 * Is this a <code>\write</code> event?
	 * 
	 * @return
	 */
	boolean isWrite();
}
