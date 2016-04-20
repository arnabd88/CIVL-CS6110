package edu.udel.cis.vsl.civl.semantics.common;

import java.util.Collection;
import java.util.LinkedList;

import edu.udel.cis.vsl.civl.semantics.IF.Transition;
import edu.udel.cis.vsl.civl.semantics.IF.TransitionSequence;
import edu.udel.cis.vsl.civl.state.IF.State;

/**
 * A transition sequence contains a list of transitions and the state from which
 * they emanate.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * @author Manchun Zheng (zmanchun)
 */
public class CommonTransitionSequence implements TransitionSequence {

	/* *************************** Instance Fields ************************* */

	/**
	 * All the transitions emanating from a certain state.
	 */
	private LinkedList<Transition> transitions;

	/**
	 * This is the state from which all the transitions in the sequence emanate.
	 */
	private State state;

	/**
	 * The number of elements removed from this sequence since it was created.
	 */
	private int numRemoved = 0;

	private boolean containingAllEnabled = false;

	/* ***************************** Constructors ************************** */

	/**
	 * Create an empty transition sequence.
	 * 
	 * @param state
	 *            The state that all transitions of this sequence emanate from.
	 */
	public CommonTransitionSequence(State state, boolean allEnabled) {
		this.state = state;
		this.transitions = new LinkedList<Transition>();
		this.containingAllEnabled = allEnabled;
	}

	/* ******************* Methods from TransitionSequence ***************** */

	@Override
	public Transition remove() {
		Transition result = transitions.remove();

		numRemoved++;
		return result;
	}

	@Override
	public int numRemoved() {
		return numRemoved;
	}

	@Override
	public State state() {
		return state;
	}

	@Override
	public void addAll(Collection<Transition> transitions) {
		this.transitions.addAll(transitions);
	}

	@Override
	public int size() {
		return this.transitions.size();
	}

	@Override
	public boolean isEmpty() {
		return this.transitions.isEmpty();
	}

	@Override
	public Transition peek() {
		return this.transitions.peek();
	}

	/* ************************* Methods from Object *********************** */

	@Override
	public String toString() {
		StringBuffer result = new StringBuffer();

		result.append(state.toString());
		for (Transition transition : this.transitions) {
			result.append(":\n");
			result.append(transition.toString());
		}
		return result.toString();
	}

	@Override
	public boolean containsAllEnabled() {
		return this.containingAllEnabled;
	}

	@Override
	public Collection<Transition> transitions() {
		return transitions;
	}

	@Override
	public void setContainingAllEnabled(boolean value) {
		this.containingAllEnabled = value;
	}
}
