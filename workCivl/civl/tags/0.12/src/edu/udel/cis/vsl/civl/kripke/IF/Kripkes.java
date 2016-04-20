package edu.udel.cis.vsl.civl.kripke.IF;

import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.kripke.common.CommonLibraryEnablerLoader;
import edu.udel.cis.vsl.civl.kripke.common.CommonStateManager;
import edu.udel.cis.vsl.civl.kripke.common.PointeredEnabler;
import edu.udel.cis.vsl.civl.log.IF.CIVLErrorLogger;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluator;
import edu.udel.cis.vsl.civl.semantics.IF.Executor;
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
	 * @param showAmpleSet
	 *            The flag of turning on or off the option to show ample set.
	 * @param showAmpleSetWtStates
	 *            The flag of turning on or off the option to show ample set
	 *            with the state.
	 * @param libLoader
	 *            The library enabler loader to be used.
	 * @param errorLogger
	 *            The error logger to be used.
	 * @return The new enabler created.
	 */
	public static Enabler newEnabler(StateFactory stateFactory,
			Evaluator evaluator, LibraryEnablerLoader libLoader,
			CIVLErrorLogger errorLogger, CIVLConfiguration civlConfig) {
		return new PointeredEnabler(stateFactory, evaluator, libLoader,
				errorLogger, civlConfig);
	}

	/**
	 * Creates a new instance of library enabler loader.
	 * 
	 * @return The new library enabler loader created.
	 */
	public static LibraryEnablerLoader newLibraryEnablerLoader() {
		return new CommonLibraryEnablerLoader();
	}

	/**
	 * Creates a new instance of state manager.
	 * 
	 * @param enabler
	 *            The enabler to be used.
	 * @param executor
	 *            The executor to be used.
	 * @param out
	 *            The printing stream to be used.
	 * @param verbose
	 *            The flag to turn on or off verbose output.
	 * @param debug
	 *            The flag to turn on or off debugging output.
	 * @param showStates
	 *            The flag to turn on or off the option of showing all states.
	 * @param showSavedStates
	 *            The flag to turn on or off the option of showing only saved
	 *            states.
	 * @param showTransitions
	 *            The flag to turn on or off the option of showing transitions.
	 * @param saveStates
	 *            The flag to enable or disable saving states.
	 * @param simplify
	 *            The flag to enable or disable simplifying states.
	 * @param errorLogger
	 *            The error logger to be used.
	 * @return
	 */
	public static StateManager newStateManager(Enabler enabler,
			Executor executor, CIVLErrorLogger errorLogger,
			CIVLConfiguration config) {
		return new CommonStateManager(enabler, executor, errorLogger, config);
	}
}
