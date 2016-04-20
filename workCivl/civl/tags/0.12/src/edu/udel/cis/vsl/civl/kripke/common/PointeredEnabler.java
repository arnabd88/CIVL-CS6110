package edu.udel.cis.vsl.civl.kripke.common;

import java.util.LinkedList;
import java.util.List;

import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.kripke.IF.Enabler;
import edu.udel.cis.vsl.civl.kripke.IF.LibraryEnablerLoader;
import edu.udel.cis.vsl.civl.log.IF.CIVLErrorLogger;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluator;
import edu.udel.cis.vsl.civl.semantics.IF.Semantics;
import edu.udel.cis.vsl.civl.semantics.IF.TransitionSequence;
import edu.udel.cis.vsl.civl.state.IF.ProcessState;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.StateFactory;
import edu.udel.cis.vsl.gmc.EnablerIF;

/**
 * EnablerPOR implements {@link EnablerIF} for CIVL models. Its basic
 * functionality is to obtain the set of enabled transitions of a certain state,
 * using the new POR as discussed in Feb 2014.
 * 
 * @author Manchun Zheng (zmanchun)
 */
public class PointeredEnabler extends CommonEnabler implements Enabler {

	/* ***************************** Constructors ************************** */

	/**
	 * Create a new instance of enabler that implements the POR based on impact
	 * memory units.
	 * 
	 * @param transitionFactory
	 *            The unique transition factory used in the system to create
	 *            transitions.
	 * @param evaluator
	 *            The unique evaluator used in the system to evaluate
	 *            expressions at a given state.
	 * @param executor
	 *            The unique executor used in the system to execute statements
	 *            at a certain state.
	 * @param showAmpleSet
	 *            The option to enable/disable the printing of ample sets at
	 *            each state.
	 */
	public PointeredEnabler(StateFactory stateFactory, Evaluator evaluator,
			LibraryEnablerLoader libLoader, CIVLErrorLogger errorLogger,
			CIVLConfiguration civlConfig) {
		super(stateFactory, evaluator, libLoader, errorLogger, civlConfig);
	}

	/* ************************* Methods from Enabler ********************** */

	/**
	 * The partial order reduction computes the set of processes that impact a
	 * set of memory units exclusively accessed by other processes.
	 * 
	 * @param state
	 *            The state to work with.
	 * @return The enabled transitions as an instance of TransitionSequence.
	 */
	@Override
	protected TransitionSequence enabledTransitionsPOR(State state) {
		TransitionSequence transitions = Semantics.newTransitionSequence(state);
		AmpleSetWorker ampleWorker = new AmpleSetWorker(state, this, evaluator,
				debugging, debugOut);
		List<ProcessState> processStates = new LinkedList<>(
				ampleWorker.ampleProcesses());// compute ample processes

		if (debugging || showAmpleSet) {
			if (processStates.size() > 1) {
				debugOut.print("ample processes at state "
						+ state.getCanonicId() + ":\t");
				for (ProcessState p : processStates) {
					debugOut.print(p.getPid() + "\t");
				}
				debugOut.println();
				if (!debugging && showAmpleSetWtStates)
					// state.print(debugOut);
					// this.stateFactory.printState(debugOut, state);
					debugOut.print(evaluator.symbolicUtility().stateToString(
							state));
			}
		}
		// Compute the ample set (of transitions)
		for (ProcessState p : processStates) {
			transitions.addAll(enabledTransitionsOfProcess(state, p.getPid()));
		}
		return transitions;
	}

}
