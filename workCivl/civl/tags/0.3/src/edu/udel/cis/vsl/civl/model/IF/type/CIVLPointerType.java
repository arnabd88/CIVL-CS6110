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

	/**
	 * Returns the highest scope in the static scope hierarchy in which the
	 * target of this pointer could be declared.
	 */
	Scope getRegion();

}
