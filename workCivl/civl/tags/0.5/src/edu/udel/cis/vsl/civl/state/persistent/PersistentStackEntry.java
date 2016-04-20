/**
 * 
 */
package edu.udel.cis.vsl.civl.state.persistent;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.state.IF.StackEntry;

/**
 * A StackEntry represents an entry on the call stack of a process, also known
 * as an "activation frame". In this simple immutable representation, there are
 * two essential fields: location and scope.
 * 
 * 
 * @author Timothy K. Zirkel (zirkel)
 * @author Stpehen F. Siegel (siegel)
 * 
 */
public class PersistentStackEntry implements StackEntry {

	/************************ Instance Fields ************************/

	/**
	 * Has the hashcode been computed and cached?
	 */
	private boolean hashed = false;

	/**
	 * The hashcode of this object. Since it is immutable, we can cache it. If
	 * the hash code has not yet been computed, this will be -1.
	 */
	private int hashCode = -1;

	/**
	 * The (static) location for this stack entry. This corresponds to a value
	 * of the "program counter". May be null.
	 */
	private Location location;

	/**
	 * The dynamic scope for this stack entry. Should be a nonnegative int.
	 */
	private int scope;

	/************************** Constructors *************************/

	/**
	 * A stack entry has a location and dynamic scope. It is put on the call
	 * stack when a process calls a function. The location of the top entry in
	 * the stack is updated as it executes.
	 * 
	 * @param location
	 *            the location for this entry; may be null
	 * @param scope
	 *            the dynamic scope of this entry, a nonnegative int
	 */
	PersistentStackEntry(Location location, int scope) {
		this.location = location;
		this.scope = scope;
	}

	/******************** Package-private Methods ********************/

	/**
	 * Returns a stack entry which is same as this one but with given location
	 * value.
	 * 
	 * @param location
	 *            the new location value
	 * @return a PersistentStackEntry with same scope but given location
	 */
	PersistentStackEntry setLocation(Location location) {
		return location == this.location ? this : new PersistentStackEntry(
				location, scope);
	}

	/**
	 * Returns a stack entry which is same as this one but with given scope
	 * value.
	 * 
	 * @param scope
	 *            the new scope value
	 * @return a PersistentStackEntry with same location but given scope
	 */
	PersistentStackEntry setScope(int scope) {
		return scope == this.scope ? this : new PersistentStackEntry(location,
				scope);
	}

	/*********************** Methods from Object *********************/

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
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj instanceof PersistentStackEntry) {
			PersistentStackEntry that = (PersistentStackEntry) obj;

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

		return "Frame[function=" + location.function().name() + ", location="
				+ location.id() + locationString + ", scope=" + scope + "]";
	}

	/********************* Methods from StackEntry *******************/

	@Override
	public Location location() {
		return location;
	}

	@Override
	public int scope() {
		return scope;
	}
}
