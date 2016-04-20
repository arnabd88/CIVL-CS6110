/**
 * 
 */
package edu.udel.cis.vsl.civl.model.IF.type;

import edu.udel.cis.vsl.civl.model.IF.expression.Expression;

/**
 * The type for an array of T where the extent is specified.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public interface CIVLCompleteArrayType extends CIVLArrayType {

	/**
	 * 
	 * @return The extent of this array.
	 */
	Expression extent();

}
