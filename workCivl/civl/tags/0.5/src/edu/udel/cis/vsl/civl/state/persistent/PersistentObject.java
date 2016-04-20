package edu.udel.cis.vsl.civl.state.persistent;

import java.util.Map;

import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;

/**
 * The root class for persistent (immutable) objects. Provides partial
 * functionality used by all such objects. This includes: caching of hash codes,
 * an efficient skeleton equals method, and a canonize method supporting the
 * Flyweight Pattern. Subclasses need to implement the abstract methods.
 * 
 * @author siegel
 * 
 */
public abstract class PersistentObject {

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
	 * Is this object the unique representative of its equivalence class? Used
	 * for the Flyweight Pattern, to flyweight these objects.
	 */
	private boolean canonic = false;

	/*********************** Abstract Methods ************************/

	/**
	 * Computes the hash code for this object. The actual hashCode method uses
	 * this one in case the hash code has not been cached.
	 * 
	 * @return the hash code for this object
	 */
	protected abstract int computeHashCode();

	/**
	 * Determines whether the given persistent object is equal to this one. May
	 * assume this object is not the same as (==) obj. This method is used by
	 * the actual equals method, which has various optimizations.
	 * 
	 * @param that
	 *            a persistent object which is not == this
	 * @return true iff the two objects should be considered "equal"
	 */
	protected abstract boolean computeEquals(PersistentObject obj);

	/**
	 * Replaces any fields of this object which are persistent objects with
	 * their canonic representatives. This method is used by the canonize method
	 * which is used to make this object canonic.
	 * 
	 * @param universe
	 *            the symbolic universe used for creating canonic symbolic
	 *            expressions and performing substitutions, etc.
	 * @param canonicMap
	 *            the map consisting of all pairs (X,X) where X is a canonic
	 *            persistent object
	 */
	protected abstract void canonizeChildren(SymbolicUniverse universe,
			Map<PersistentObject, PersistentObject> canonicMap);

	/******************** Package-private Methods ********************/

	/**
	 * Is this object the canonical representative of its equivalence class
	 * under the "equals" method?
	 * 
	 * @return true iff this is canonic
	 */
	boolean isCanonic() {
		return canonic;
	}

	/*********************** Protected Methods ***********************/

	/**
	 * Returns the unique representative of the equivalence class (under
	 * "equals") containing this persistent object. The canonicMap is assumed to
	 * consist of all pairs (X,X) where X is a canonic object. This method will
	 * look in this map to see if there is an entry with X equal to this, in
	 * which case X will be returned. Otherwise this object will be declared to
	 * be the canonic representative of its equivalence class and will be made
	 * canonic (using method {@link #canonizeChildren(SymbolicUniverse, Map)})
	 * and entered into canonicMap.
	 * 
	 * @param universe
	 *            symbolic universe used to make symbolic expressions canonic
	 * @param canonicMap
	 *            the map consisting of all pairs (X,X) where X is a canonic
	 *            persistent object
	 * @return the canonic representative of the equivalence class (under
	 *         "equals") containing this
	 */
	protected PersistentObject canonize(SymbolicUniverse universe,
			Map<PersistentObject, PersistentObject> canonicMap) {
		if (canonic)
			return this;
		else {
			PersistentObject canonicObject = canonicMap.get(this);

			if (canonicObject == null) {
				canonizeChildren(universe, canonicMap);
				canonic = true;
				canonicMap.put(this, this);
				canonicObject = this;
			}
			return canonicObject;
		}
	}

	/********************** Methods from Object **********************/

	/**
	 * Implementation of hash code that looks to see if the hash code has been
	 * previously computed and cached. If not, it computes the hash code by
	 * invoking {@link #computeHashCode()} and caching it.
	 * 
	 * @return the hash code of this object
	 */
	@Override
	public int hashCode() {
		if (!hashed) {
			hashCode = computeHashCode();
			hashed = true;
		}
		return hashCode;
	}

	/**
	 * Optimized implementation of equals based on the following: (1) if this ==
	 * obj, objects are equal; (2) if both objects are persistent and canonic,
	 * then they are equal iff they are the same (==); if both objects are
	 * persistent and have cached hash codes which are not equal, they are not
	 * equal. If none of these yields the answer, method
	 * {@link #computeEquals(PersistentObject)} is invoked.
	 * 
	 * @param obj
	 *            any object
	 * @return true iff this is considered "equal" to that
	 */
	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj instanceof PersistentObject) {
			PersistentObject that = (PersistentObject) obj;

			if (canonic && that.canonic)
				return false;
			if (hashed && that.hashed && hashCode != that.hashCode)
				return false;
			return computeEquals(that);
		}
		return false;
	}
}
