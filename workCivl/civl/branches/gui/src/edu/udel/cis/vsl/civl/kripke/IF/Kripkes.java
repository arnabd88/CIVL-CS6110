package edu.udel.cis.vsl.civl.kripke.IF;

import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.kripke.common.CommonLibraryEnablerLoader;
import edu.udel.cis.vsl.civl.kripke.common.CommonStateManager;
import edu.udel.cis.vsl.civl.kripke.common.PointeredEnabler;
import edu.udel.cis.vsl.civl.log.IF.CIVLErrorLogger;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluator;
import edu.udel.cis.vsl.civl.semantics.IF.Executor;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryEvaluatorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.SymbolicAnalyzer;
import edu.udel.cis.vsl.civl.state.IF.MemoryUnitFactory;
import edu.udel.cis.vsl.civl.state.IF.StateFactory;

/**
 * This is the entry point of the module <strong>kripke</strong>.
 * 
 * @author Manchun Zheng
 * 
 */
public class Kripkes {

	/**
	 * Creates a new instance of enabler.
	 * 
	 * @param stateFactory
	 *            The state factory to be used.
	 * @param evaluator
	 *            The evaluator to be used.
	 * @param symbolicAnalyzer
	 *            The symbolic analyzer used in the system.
	 * @param memUnitFactory
	 *            The memory unit factory for memory analysis.
	 * @param libLoader
	 *            The library enabler loader to be used.
	 * @param errorLogger
	 *            The error logger to be used.
	 * @param civlConfig
	 *            The configuration of the CIVL model.
	 * @return The new enabler created.
	 */
	public static Enabler newEnabler(StateFactory stateFactory,
			Evaluator evaluator, SymbolicAnalyzer symbolicAnalyzer,
			MemoryUnitFactory memUnitFactory, LibraryEnablerLoader libLoader,
			CIVLErrorLogger errorLogger, CIVLConfiguration civlConfig) {
		return new PointeredEnabler(stateFactory, evaluator, symbolicAnalyzer,
				memUnitFactory, libLoader, errorLogger, civlConfig);
	}

	/**
	 * Creates a new instance of library enabler loader.
	 * 
	 * @param libEvaluatorLoader
	 *            the library evaluator loader
	 * @param civlConfig
	 *            the CIVL configuration
	 * 
	 * @return The new library enabler loader created.
	 */
	public static LibraryEnablerLoader newLibraryEnablerLoader(
			LibraryEvaluatorLoader libEvaluatorLoader,
			CIVLConfiguration civlConfig) {
		return new CommonLibraryEnablerLoader(libEvaluatorLoader, civlConfig);
	}

	/**
	 * Creates a new instance of state manager.
	 * 
	 * @param enabler
	 *            The enabler to be used.
	 * @param executor
	 *            The executor to be used.
	 * @param symbolicAnalyzer
	 *            The symbolic analyzer to be used.
	 * @param errorLogger
	 *            The error logger to be used.
	 * @param config
	 *            The configuration of the CIVL model.
	 * @return The new state manager created.
	 */
	public static StateManager newStateManager(Enabler enabler,
			Executor executor, SymbolicAnalyzer symbolicAnalyzer,
			CIVLErrorLogger errorLogger, CIVLConfiguration config) {
		return new CommonStateManager(enabler, executor, symbolicAnalyzer,
				errorLogger, config);
	}
}
