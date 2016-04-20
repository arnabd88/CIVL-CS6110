package edu.udel.cis.vsl.civl.library.asserts;

import java.io.PrintStream;

import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.kripke.IF.Enabler;
import edu.udel.cis.vsl.civl.kripke.IF.LibraryEnabler;
import edu.udel.cis.vsl.civl.library.IF.BaseLibraryEnabler;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluator;

public class LibassertsEnabler extends BaseLibraryEnabler implements
		LibraryEnabler {

	public LibassertsEnabler(String name, Enabler primaryEnabler,
			Evaluator evaluator, PrintStream output, ModelFactory modelFactory,
			SymbolicUtility symbolicUtil) {
		super(name, primaryEnabler, evaluator, output, modelFactory,
				symbolicUtil);
	}

}
