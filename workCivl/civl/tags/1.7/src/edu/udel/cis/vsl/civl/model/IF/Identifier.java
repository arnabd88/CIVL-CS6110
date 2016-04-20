/**
 * 
 */
package edu.udel.cis.vsl.civl.model.IF;

import edu.udel.cis.vsl.sarl.IF.object.StringObject;

/**
 * An identifier. Used for names of variables, functions, etc.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public interface Identifier extends Sourceable {

	/**
	 * @return The name associated with this identifier.
	 */
	public String name();

	/**
	 * The name as a SARL string object.
	 * 
	 * @return name as string object
	 */
	public StringObject stringObject();
}
