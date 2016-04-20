package edu.udel.cis.vsl.civl.library.stdio;

import java.io.PrintStream;

import edu.udel.cis.vsl.civl.kripke.Enabler;
import edu.udel.cis.vsl.civl.library.CommonLibraryEnabler;
import edu.udel.cis.vsl.civl.library.IF.LibraryEnabler;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;

/**
 * Implementation of the enabler-related logics for system functions declared
 * stdio.h.
 * 
 * @author Manchun Zheng (zmanchun)
 * 
 */
public class LibstdioEnabler extends CommonLibraryEnabler implements
		LibraryEnabler {

	/* **************************** Constructors *************************** */

	/**
	 * Creates a new instance of the library enabler for stdio.h.
	 * 
	 * @param primaryEnabler
	 *            The enabler for normal CIVL execution.
	 * @param output
	 *            The output stream to be used in the enabler.
	 * @param modelFactory
	 *            The model factory of the system.
	 */
	public LibstdioEnabler(Enabler primaryEnabler, PrintStream output,
			ModelFactory modelFactory) {
		super(primaryEnabler, output, modelFactory);
	}
	
	/* ************************ Methods from Library *********************** */

	@Override
	public String name() {
		return "stdio";
	}

}
