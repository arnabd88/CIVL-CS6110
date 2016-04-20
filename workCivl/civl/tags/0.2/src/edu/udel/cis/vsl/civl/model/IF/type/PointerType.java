/**
 * 
 */
package edu.udel.cis.vsl.civl.model.IF.type;


/**
 * Type of a pointer.
 * 
 * @author zirkel
 */
public interface PointerType extends Type {

	/** Returns the type of element pointed to. Result could be "void", as in C */
	Type baseType();
}
