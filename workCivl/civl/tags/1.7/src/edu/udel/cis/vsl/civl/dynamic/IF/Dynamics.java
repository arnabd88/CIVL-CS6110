package edu.udel.cis.vsl.civl.dynamic.IF;

import edu.udel.cis.vsl.civl.dynamic.common.CommonSymbolicUtility;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;

/**
 * Entry point of the module <strong>dynamic</strong>.
 * 
 * @author Manchun Zheng
 * 
 */
public class Dynamics {

	/**
	 * Creates a new instance of symbolic utility.
	 * 
	 * @param universe
	 *            The symbolic universe to be used.
	 * @param modelFactory
	 *            The model factory to be used.
	 * @return The new symbolic utility created.
	 */
	public static SymbolicUtility newSymbolicUtility(SymbolicUniverse universe,
			ModelFactory modelFactory) {
		return new CommonSymbolicUtility(universe, modelFactory);
	}
}
