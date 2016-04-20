package edu.udel.cis.vsl.civl.model.IF.contract;

/**
 * This represents a composite event, which could be a
 * union/difference/intersect of another two depends events.
 * 
 * @author Manchun Zheng
 *
 */
public interface CompositeEvent extends DependsEvent {
	public enum CompositeEventOperator {
		UNION, DIFFERENCE, INTERSECT
	}

	/**
	 * Returns the left operand.
	 * 
	 * @return
	 */
	DependsEvent left();

	/**
	 * Returns the right operand
	 * 
	 * @return
	 */
	DependsEvent right();

	/**
	 * Returns the operator.
	 * 
	 * @return
	 */
	CompositeEventOperator operator();
}
