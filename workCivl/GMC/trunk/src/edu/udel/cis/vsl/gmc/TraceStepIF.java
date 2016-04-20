package edu.udel.cis.vsl.gmc;

/**
 * A TraceStepIF represents the execution result of nextState of StateManagerIF.
 * See {@link StateManagerIF#nextState(STATE, TRANSITION)}.
 * 
 * @author Manchun Zheng
 * 
 * @param <TRANSITION>
 *            the type used to represent transitions in the state-transition
 *            system being analyzed
 * @param <STATE>
 *            the type used to represent states in the state-transition system
 *            being analyzed
 */
public interface TraceStepIF<TRANSITION, STATE> {
	/**
	 * Returns the resulting state of the trace step.
	 * 
	 * @return the resulting state of the trace step.
	 */
	STATE getFinalState();
}
