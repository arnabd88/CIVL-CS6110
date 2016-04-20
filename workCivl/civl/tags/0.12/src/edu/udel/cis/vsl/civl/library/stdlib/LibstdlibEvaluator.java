package edu.udel.cis.vsl.civl.library.stdlib;

import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.library.IF.BaseLibraryEvaluator;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluator;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryEvaluator;

public class LibstdlibEvaluator extends BaseLibraryEvaluator implements
		LibraryEvaluator {

	public LibstdlibEvaluator(String name, Evaluator evaluator, ModelFactory modelFactory,
			SymbolicUtility symbolicUtil) {
		super(name, evaluator, modelFactory, symbolicUtil);
	}
}
