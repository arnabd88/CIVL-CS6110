package edu.udel.cis.vsl.civl.library.stdlib;

import java.io.PrintStream;

import edu.udel.cis.vsl.civl.kripke.Enabler;
import edu.udel.cis.vsl.civl.library.CommonLibraryEnabler;
import edu.udel.cis.vsl.civl.library.IF.LibraryEnabler;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;

/**
 * Implementation of the enabler-related logics for system functions declared
 * stdlib.h.
 * 
 * @author Manchun Zheng (zmanchun)
 * 
 */
public class LibstdlibEnabler extends CommonLibraryEnabler implements
		LibraryEnabler {

	/* **************************** Constructors *************************** */

	/**
	 * Creates a new instance of the library enabler for stdlib.h.
	 * 
	 * @param primaryEnabler
	 *            The enabler for normal CIVL execution.
	 * @param output
	 *            The output stream to be used in the enabler.
	 * @param modelFactory
	 *            The model factory of the system.
	 */
	public LibstdlibEnabler(Enabler primaryEnabler, PrintStream output,
			ModelFactory modelFactory) {
		super(primaryEnabler, output, modelFactory);
	}

	/* ************************ Methods from Library *********************** */

	@Override
	public String name() {
		return "stdlib";
	}

}
