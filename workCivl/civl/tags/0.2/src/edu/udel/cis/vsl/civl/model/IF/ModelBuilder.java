/**
 * 
 */
package edu.udel.cis.vsl.civl.model.IF;

import edu.udel.cis.vsl.abc.ast.IF.AST;

/**
 * Class to provide translation from an AST to a model.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public interface ModelBuilder {

	/**
	 * @return The model factory used by this model builder.
	 */
	public ModelFactory factory();
	/**
	 * Build the model.
	 * 
	 * @param unit
	 *            The translation unit for the AST.
	 * @return The model.
	 */
	public Model buildModel(AST unit);
	
}
