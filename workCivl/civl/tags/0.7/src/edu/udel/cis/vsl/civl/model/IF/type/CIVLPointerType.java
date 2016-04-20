/**
 * 
 */
package edu.udel.cis.vsl.civl.model.IF.type;

import edu.udel.cis.vsl.civl.model.IF.Scope;

/**
 * Type of a pointer.
 * 
 * @author zirkel
 */
public interface CIVLPointerType extends CIVLType {

	/** Returns the type of element pointed to. Result could be "void", as in C */
	CIVLType baseType();

	// TODO: Since we can't expand all of these statically, we need to have some
	// kind of dynamic representation of what the region will be. Maybe a
	// "scope expression" or something similar. Might need to be more
	// complicated to handle expression like join(s0,s1), etc.
	/**
	 * Returns the highest scope in the static scope hierarchy in which the
	 * target of this pointer could be declared.
	 */
	Scope getRegion();

}
