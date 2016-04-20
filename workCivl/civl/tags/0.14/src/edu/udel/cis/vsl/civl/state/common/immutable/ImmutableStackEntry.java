/**
 * 
 */
package edu.udel.cis.vsl.civl.state.common.immutable;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.state.IF.StackEntry;

/**
 * A stack entry has a location and dynamic scope ID. It is put on the call
 * stack when a process calls a function.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * @author Stephen F. Siegel (siegel)
 * 
 */
public class ImmutableStackEntry implements StackEntry {

	/* ************************** Instance Fields ************************** */

	/**
	 * The cached hash code of this object.
	 */
	private int hashCode = -1;

	/**
	 * Has the hash code been computed and cached?
	 */
	private boolean hashed = false;

	/**
	 * The static location in the function that is execution.
	 */
	private Location location;

	/**
	 * The ID of the dynamic scope in which the execution is taking place.
	 */
	private int dyscopeId;

	/**
	 * The identifier of the dynamic scope, which is not part of the state.
	 */
	private int dyscopeIdentifier;

	/* **************************** Constructors *************************** */

	/**
	 * Constructs new stack entry with given location and scope.
	 * 
	 * @param location
	 *            The target location of the function call. i.e. where execution
	 *            will continue after the function returns.
	 * @param dyscopeId
	 *            The dynamic scope of the process at the time of the function
	 *            call.
	 */
	ImmutableStackEntry(Location location, int dyscopeId, int dyscopeIdentifier) {
		this.location = location;
		this.dyscopeId = dyscopeId;
		this.dyscopeIdentifier = dyscopeIdentifier;
	}

	/* ********************** Methods from StackEntry ********************** */

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
		return dyscopeId;
	}

	@Override
	public int dyscopeIdentifier() {
		return this.dyscopeIdentifier;
	}

	/* ************************* Methods from Object ************************* */

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
			if (dyscopeId != that.dyscopeId)
				return false;
			return true;
		}
		return false;
	}

	@Override
	public int hashCode() {
		if (!hashed) {
			hashCode = (31 * dyscopeId)
					^ (101 * (location == null ? 0 : location.hashCode()));
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
				+ location.id() + locationString + ", dyscope=d"
				+ dyscopeIdentifier + "]";
	}

}
