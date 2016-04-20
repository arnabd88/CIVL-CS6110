/**
 * 
 */
package edu.udel.cis.vsl.civl.model.common;

import edu.udel.cis.vsl.abc.program.IF.Program;
import edu.udel.cis.vsl.civl.model.IF.Model;
import edu.udel.cis.vsl.civl.model.IF.ModelBuilder;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.gmc.CommandLineException;
import edu.udel.cis.vsl.gmc.GMCConfiguration;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;

/**
 * Class to provide translation from an ABC AST to a CIVL model.
 * 
 * @author zirkeltk
 * 
 */
public class CommonModelBuilder implements ModelBuilder {

	// Fields..........................................................

	/**
	 * The factory used to create new Model components.
	 */
	private ModelFactory factory;

	// Constructors....................................................

	/**
	 * Constructs new instance of CommonModelBuilder, creating instance of
	 * ModelFactory in the process, and sets up system functions.
	 * 
	 * @param universe
	 *            The symbolic universe
	 */
	public CommonModelBuilder(SymbolicUniverse universe) {
		factory = new CommonModelFactory(universe);
	}

	// Exported Methods................................................

	@Override
	public Model buildModel(GMCConfiguration config, Program program,
			String name) throws CommandLineException {
		ModelBuilderWorker worker = new ModelBuilderWorker(config, factory,
				program, name);

		worker.buildModel();
		return worker.getModel();
	}

	@Override
	public ModelFactory factory() {
		return factory;
	}

}
