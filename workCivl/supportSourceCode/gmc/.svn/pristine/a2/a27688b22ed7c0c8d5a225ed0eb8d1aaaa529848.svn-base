package edu.udel.cis.vsl.gmc;

/**
 * General interface for an object which can select one enabled transition from
 * the set of enabled transitions at any state.
 * 
 * @author Stephen F. Siegel
 * 
 * @param <STATE>
 *            the type of states in the state-transition system
 * @param <TRANSITION>
 *            the type of transitions in the state-transition system
 */
public interface TransitionChooser<STATE, TRANSITION> {

	/**
	 * Using some protocol, chooses one of the transitions enabled at the given
	 * state. If there are no enabled transitions, returns null.
	 * 
	 * @param state
	 *            a state
	 * @return a transition enabled at that state, or null if there is none
	 * @throws MisguidedExecutionException
	 *             if a transition cannot be selected for some reason
	 */
	TRANSITION chooseEnabledTransition(STATE state)
			throws MisguidedExecutionException;

}
