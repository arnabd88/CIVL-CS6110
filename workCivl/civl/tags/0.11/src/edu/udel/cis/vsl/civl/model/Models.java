/**
 * 
 */
package edu.udel.cis.vsl.civl.model;

import edu.udel.cis.vsl.civl.model.IF.ModelBuilder;
import edu.udel.cis.vsl.civl.model.IF.ModelCombiner;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.common.CommonModelBuilder;
import edu.udel.cis.vsl.civl.model.common.CommonModelCombiner;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;

/**
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public class Models {

	public static ModelBuilder newModelBuilder(SymbolicUniverse universe) {
		return new CommonModelBuilder(universe);
	}

	public static ModelBuilder newModelBuilder(ModelFactory factory) {
		return new CommonModelBuilder(factory.universe(), factory);
	}

	public static ModelCombiner newModelCombiner(ModelFactory factory) {
		return new CommonModelCombiner(factory);
	}

}
