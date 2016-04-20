package edu.udel.cis.vsl.civl.model.IF.contract;

import edu.udel.cis.vsl.civl.model.IF.Sourceable;

/**
 * This represents an event which is used as one argument of the
 * <code>depends</code> clause.
 * 
 * @author Manchun Zheng
 *
 */
public interface DependsEvent extends Sourceable {
	public enum DependsEventKind {
		READ, WRITE, CALL, COMPOSITE, ANYACT, NOACT
	}

	/**
	 * Returns the kind of this event.
	 * 
	 * @return
	 */
	DependsEventKind dependsEventKind();

	/**
	 * Does this event equals to that event?
	 * 
	 * @param that
	 * @return
	 */
	boolean equalsWork(DependsEvent that);
}
