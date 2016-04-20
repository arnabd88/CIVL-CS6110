package edu.udel.cis.vsl.civl.state.IF;

import edu.udel.cis.vsl.sarl.IF.expr.ReferenceExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;

public interface MemoryUnitFactory {

	/**
	 * Adds a memory unit to a memory unit set.
	 * 
	 * @param muSet
	 *            the memory unit set which is to be added to a new element
	 * @param mu
	 *            the memory unit to be added to the given memory unit set
	 * @return the new memory unit set after adding the given memory unit
	 */
	void add(MemoryUnitSet muSet, MemoryUnit mu);

	void add(MemoryUnitSet muSet, SymbolicExpression pointer);

	/**
	 * Return the "canonical" version of the given memory unit set.
	 * 
	 * The memory unit set returned will satisfy all of the following:
	 * <ul>
	 * <li>it will be observationally equivalent to the given memory unit set,
	 * i.e., there is no way a CIVL-C program can distinguish between the two
	 * memory unit sets</li>
	 * <li>the memory unit set returned will be the unique representative of its
	 * equivalence class, i.e., if this method is invoked with two equivalent
	 * memory unit sets, it will return the same object</li>
	 * </ul>
	 * 
	 * @param muSet
	 *            any non-null memory unit set
	 * @return the canonical version of the given memory unit set
	 */
	MemoryUnitSet canonic(MemoryUnitSet muSet);

	/**
	 * This is an over-approximation method to test if two memory units have any
	 * intersection. It returns true if the two memory units may or may NOT have
	 * any intersection.
	 * 
	 * @param mu1
	 *            the first memory unit
	 * @param mu2
	 *            the second memory unit
	 * @return
	 */
	boolean isJoint(MemoryUnit mu1, MemoryUnit mu2);

	/**
	 * This is an over-approximation method to test if two memory unit sets have
	 * any intersection. It returns true if the two memory unit sets may or may
	 * NOT have any intersection.
	 * 
	 * @param muSet1
	 *            the first memory unit
	 * @param muSet2
	 *            the second memory unit
	 * @return
	 */
	boolean isJoint(MemoryUnitSet muSet1, MemoryUnitSet muSet2);

	/**
	 * This is an over-approximation method of membership testing. If muSet
	 * doesn't contain mu, returns false. If muSet may or may not contain mu,
	 * returns true.
	 * 
	 * @param muSet
	 *            the memory unit set
	 * @param mu
	 *            the memory unit to be tested for membership
	 * @return false if the given memory unit set does not contain the given
	 *         memory unit; returns true if it may or may not contain the memory
	 *         unit.
	 */
	boolean isJoint(MemoryUnitSet muSet, MemoryUnit mu);

	/**
	 * This is an over-approximation method of union. It always returns a super
	 * set of the union of the given memory unit sets.
	 * 
	 * @param muSet1
	 *            the first memory unit set
	 * @param muSet2
	 *            the second memory unit set
	 * @return
	 */
	MemoryUnitSet union(MemoryUnitSet muSet1, MemoryUnitSet muSet2);

	/**
	 * This is an over-approximation method of intersection. It always returns a
	 * super set of the intersection of the given memory unit sets.
	 * 
	 * @param muSet1
	 *            the first memory unit set
	 * @param muSet2
	 *            the second memory unit set
	 * @return
	 */
	MemoryUnitSet intersects(MemoryUnitSet muSet1, MemoryUnitSet muSet2);

	MemoryUnit newMemoryUnit(int dyscopeID, int varID,
			ReferenceExpression reference);

	MemoryUnitSet newMemoryUnitSet();
}
