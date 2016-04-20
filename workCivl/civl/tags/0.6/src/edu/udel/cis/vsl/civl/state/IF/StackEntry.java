package edu.udel.cis.vsl.civl.state.IF;

import edu.udel.cis.vsl.civl.model.IF.location.Location;

/**
 * An entry on a call stack of a process; also known as an "activation frame".
 * An entry records the current location and dynamic scope of a process.
 * 
 * @author siegel
 * 
 */
public interface StackEntry {

	/**
	 * Returns the static location component of this activation frame. This is
	 * the value of the "program counter".
	 * 
	 * @return the static location
	 */
	Location location();

	/**
	 * @return The dynamic scope of the process at the time of the function
	 *         call.
	 */
	int scope();
}
