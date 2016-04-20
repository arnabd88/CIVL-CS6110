package edu.udel.cis.vsl.civl.model.IF.expression.reference;

import edu.udel.cis.vsl.civl.model.IF.expression.Expression;

/**
 * This represents the reference to an array, which could be:
 * <ul>
 * <li>element</li>
 * <li>wildcard</li>
 * <li>range</li>
 * </ul>
 * 
 * @author zmanchun
 *
 */
public interface ArraySliceReference extends MemoryUnitReference {
	public enum ArraySliceKind {
		ELEMENT, WILDCARD, REG_RANGE
	}

	/**
	 * Returns the index expression of the array slice.
	 * 
	 * @return
	 */
	Expression index();

	/**
	 * Returns the kind of the array slice, which could be ELEMENT, WILDCARD, or
	 * RANGE.
	 * 
	 * @return
	 */
	ArraySliceKind sliceKind();
}
