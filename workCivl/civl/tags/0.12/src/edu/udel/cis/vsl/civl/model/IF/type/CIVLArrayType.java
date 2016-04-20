package edu.udel.cis.vsl.civl.model.IF.type;

/**
 * The type for an array of T.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public interface CIVLArrayType extends CIVLType {

	/**
	 * @return The type of elements in this array.
	 */
	CIVLType elementType();

	/**
	 * 
	 * @return Is this a complete array type? (i.e. is the length specified?)
	 */
	boolean isComplete();

}
