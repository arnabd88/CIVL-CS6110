package edu.udel.cis.vsl.civl.library;

/**
 * The Library class implements the common logic of library enabler and library
 * executor.
 * 
 * @author Manchun Zheng (zmanchun)
 * 
 */
public abstract class Library {

	/**
	 * Returns the name associated to this library executor or enabler, for
	 * example, "stdio".
	 * 
	 * @return
	 */
	public abstract String name();
}
