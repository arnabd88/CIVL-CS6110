/**
 * 
 */
package edu.udel.cis.vsl.civl.transition;

import java.util.LinkedList;

import edu.udel.cis.vsl.civl.state.State;

/**
 * A transition sequence is a linked list of transitions and the state from
 * which they depart.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public class TransitionSequence extends LinkedList<Transition> {

	/**
	 * Auto-generated serialVersionUID to get rid of warning caused by extending
	 * LinkedList.
	 */
	private static final long serialVersionUID = -1765498780485391615L;
	private State state;

	/**
	 * Create an empty transition sequence.
	 * 
	 * @param state
	 *            The state of the program before this transition departs.
	 */
	public TransitionSequence(State state) {
		this.state = state;
	}

	/** The source state from which all transitions in this sequence depart. */
	public State state() {
		return state;
	}

}
