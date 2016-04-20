/**
 * 
 */
package edu.udel.cis.vsl.civl.state.immutable;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.state.IF.StackEntry;

/**
 * A stack entry has a location, dynamic scope, and (optional) variable to store
 * a return value. It is put on the call stack when a process calls a function.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public class ImmutableStackEntry implements StackEntry {

	/************************* Instance Fields *************************/

	private int hashCode = -1;

	private boolean hashed = false;

	private Location location;

	private int scope;

	/************************** Constructors *************************/

	/**
	 * A stack entry has a location, dynamic scope, and (optional) variable to
	 * store a return value. It is put on the call stack when a process calls a
	 * function.
	 * 
	 * @param location
	 *            The target location of the function call. i.e. where execution
	 *            will continue after the function returns.
	 * @param scope
	 *            The dynamic scope of the process at the time of the function
	 *            call.
	 */
	ImmutableStackEntry(Location location, int scope) {
		this.location = location;
		this.scope = scope;
	}

	/******************* Methods from StackEntry *******************/

	/**
	 * @return The target location of the function call. i.e. where execution
	 *         will continue after the function returns.
	 */
	@Override
	public Location location() {
		return location;
	}

	/**
	 * @return The dynamic scope of the process at the time of the function
	 *         call.
	 */
	@Override
	public int scope() {
		return scope;
	}

	/******************* Methods from Object *******************/
	
	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj instanceof ImmutableStackEntry) {
			ImmutableStackEntry that = (ImmutableStackEntry) obj;

			if (location == null) {
				if (that.location != null)
					return false;
			} else if (!location.equals(that.location))
				return false;
			if (scope != that.scope)
				return false;
			return true;
		}
		return false;
	}
	
	@Override
	public int hashCode() {
		if (!hashed) {
			final int prime = 31;

			hashCode = prime + (location == null ? 0 : location.hashCode());
			hashCode = prime * hashCode + scope;
			hashed = true;
		}
		return hashCode;
	}

	@Override
	public String toString() {
		CIVLSource source = location.getSource();
		String locationString = source == null ? "" : ", "
				+ source.getSummary();

		return "Frame[function=" + location.function().name() + ", location="
				+ location.id() + locationString + ", scope=" + scope + "]";
	}

}
