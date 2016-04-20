/**
 * 
 */
package edu.udel.cis.vsl.civl.model.IF;

/**
 * An abstract function is an uninterpreted mathematical function. It is used in
 * assumptions and assertions to relate values in code to the actual
 * mathematical functions they represent.
 * 
 * @author zirkel
 * 
 */
public interface AbstractFunction extends CIVLFunction {

	/**
	 * @return The total number of partial derivatives that may be taken.
	 */
	int continuity();
	
}
