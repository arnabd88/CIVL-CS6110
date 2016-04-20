/**
 * 
 */
package edu.udel.cis.vsl.civl.state;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.location.Location;

/**
 * A stack entry has a location, dynamic scope, and (optional) variable to store
 * a return value. It is put on the call stack when a process calls a function.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public class StackEntry {

	private boolean hashed = false;

	private int hashCode = -1;

	private Location location;

	private int scope;

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
	StackEntry(Location location, int scope) {
		this.location = location;
		this.scope = scope;
	}

	/**
	 * @return The target location of the function call. i.e. where execution
	 *         will continue after the function returns.
	 */
	public Location location() {
		return location;
	}

	/**
	 * @return The dynamic scope of the process at the time of the function
	 *         call.
	 */
	public int scope() {
		return scope;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.lang.Object#hashCode()
	 */
	@Override
	public int hashCode() {
		if (!hashed) {
			final int prime = 31;

			hashCode = prime + ((location == null) ? 0 : location.hashCode());
			hashCode = prime * hashCode + scope;
			hashed = true;
		}
		return hashCode;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.lang.Object#equals(java.lang.Object)
	 */
	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj instanceof StackEntry) {
			StackEntry that = (StackEntry) obj;

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
	public String toString() {
		CIVLSource source = location.getSource();
		String locationString = source == null ? "" : ", "
				+ source.getSummary();
		
//		if(location.isPurelyLocal())
//			locationString = locationString + " # ";
		
		return "Frame[function=" + location.function().name() + ", location="
				+ location.id() + locationString + ", scope=" + scope + "]";
	}

}
