package edu.udel.cis.vsl.civl.library.pointer;

import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.library.common.BaseLibraryEvaluator;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluator;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryEvaluator;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryEvaluatorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.SymbolicAnalyzer;

public class LibpointerEvaluator extends BaseLibraryEvaluator implements
		LibraryEvaluator {

	public LibpointerEvaluator(String name, Evaluator evaluator,
			ModelFactory modelFactory, SymbolicUtility symbolicUtil,
			SymbolicAnalyzer symbolicAnalyzer,
			LibraryEvaluatorLoader libEvaluatorLoader) {
		super(name, evaluator, modelFactory, symbolicUtil, symbolicAnalyzer,
				libEvaluatorLoader);
	}

}
