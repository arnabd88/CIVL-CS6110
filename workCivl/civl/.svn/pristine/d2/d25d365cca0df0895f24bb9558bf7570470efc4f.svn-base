package edu.udel.cis.vsl.civl.library.bundle;

import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.kripke.IF.Enabler;
import edu.udel.cis.vsl.civl.kripke.IF.LibraryEnabler;
import edu.udel.cis.vsl.civl.kripke.IF.LibraryEnablerLoader;
import edu.udel.cis.vsl.civl.library.common.BaseLibraryEnabler;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluator;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryEvaluatorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.SymbolicAnalyzer;

/**
 * The library enabler for bundle.cvh. Since all functions related to bundle are
 * deterministic and don't have any special logics in partial order reduction,
 * there is no need to override methods from BaseLibraryEnabler.
 * 
 * @author Manchun Zheng (zmanchun)
 * 
 */
public class LibbundleEnabler extends BaseLibraryEnabler implements
		LibraryEnabler {

	/**
	 * Creates a new instance of library enabler for bundle.cvh.
	 * 
	 * @param name
	 *            The name of the library enabler, which should be bundle.
	 * @param primaryEnabler
	 *            The CIVL enabler.
	 * @param evaluator
	 *            The CIVL evaluator.
	 * @param output
	 * @param modelFactory
	 * @param symbolicUtil
	 */
	public LibbundleEnabler(String name, Enabler primaryEnabler,
			Evaluator evaluator, ModelFactory modelFactory,
			SymbolicUtility symbolicUtil, SymbolicAnalyzer symbolicAnalyzer,
			LibraryEnablerLoader libEnablerLoader,
			LibraryEvaluatorLoader libEvaluatorLoader) {
		super(name, primaryEnabler, evaluator, modelFactory, symbolicUtil,
				symbolicAnalyzer, libEnablerLoader, libEvaluatorLoader);
	}

}
