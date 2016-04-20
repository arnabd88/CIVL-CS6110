/**
 * 
 */
package edu.udel.cis.vsl.civl.model.IF;

import edu.udel.cis.vsl.abc.program.IF.Program;

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
	 * @param program
	 *            The ABC program to translate.
	 * @return The model.
	 */
	public Model buildModel(Program program);

}
