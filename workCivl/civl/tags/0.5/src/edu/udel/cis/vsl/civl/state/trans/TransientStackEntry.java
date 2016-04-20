/**
 * 
 */
package edu.udel.cis.vsl.civl.state.trans;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.state.IF.StackEntry;

/**
 * A stack entry has a location, dynamic scope, and (optional) variable to store
 * a return value. It is put on the call stack when a process calls a function.
 * 
 * Immutable.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * @author Stephen F. Siegel (siegel)
 * 
 */
public class TransientStackEntry implements StackEntry {

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
	TransientStackEntry(Location location, int scope) {
		this.location = location;
		this.scope = scope;
	}

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

	@Override
	public int hashCode() {
		if (!hashed) {
			hashCode = (location == null ? 514229 : 31 * location.hashCode())
					^ (scope * 39916801);
			hashed = true;
		}
		return hashCode;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj instanceof TransientStackEntry) {
			TransientStackEntry that = (TransientStackEntry) obj;

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

		// if(location.isPurelyLocal())
		// locationString = locationString + " # ";

		return "Frame[function=" + location.function().name() + ", location="
				+ location.id() + locationString + ", scope=" + scope + "]";
	}

}
