/**
 * 
 */
package edu.udel.cis.vsl.civl.model.IF;

import edu.udel.cis.vsl.civl.model.common.CommonModelBuilder;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;

/**
 * This is the entry point of the module <strong>model</strong>.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public class Models {

	/**
	 * Creates a new instance of model builder.
	 * 
	 * @param universe
	 *            The symbolic universe to be used.
	 * @return The new model builder created.
	 */
	public static ModelBuilder newModelBuilder(SymbolicUniverse universe) {
		return new CommonModelBuilder(universe);
	}

	/**
	 * Creates a new instance of model builder.
	 * 
	 * @param factory
	 *            The model factory to be used.
	 * @return The new model builder created.
	 */
	public static ModelBuilder newModelBuilder(ModelFactory factory) {
		return new CommonModelBuilder(factory.universe(), factory);
	}

}
