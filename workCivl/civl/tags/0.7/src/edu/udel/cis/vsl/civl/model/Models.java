/**
 * 
 */
package edu.udel.cis.vsl.civl.model;

import edu.udel.cis.vsl.civl.model.IF.ModelBuilder;
import edu.udel.cis.vsl.civl.model.common.CommonModelBuilder;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;

/**
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public class Models {

	public static ModelBuilder newModelBuilder(SymbolicUniverse universe, boolean mpiMode) {
		return new CommonModelBuilder(universe, mpiMode);
	}

}
