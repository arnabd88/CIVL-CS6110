/**
 * 
 */
package edu.udel.cis.vsl.civl.semantics.IF;

import java.util.Collection;

import edu.udel.cis.vsl.civl.state.IF.State;

/**
 * A transition sequence contains a list of transitions and the state from which
 * they emanate.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * @author Manchun Zheng (zmanchun)
 */
public interface TransitionSequence {

	/**
	 * Retrieves and removes the head (first element) of this transition
	 * sequence.
	 * 
	 * @return The head (first element) of this transition sequence.
	 */
	Transition remove();

	/**
	 * Returns the number of transitions removed from this sequence since it was
	 * first created.
	 * 
	 * @return the number of transitions removed
	 */
	int numRemoved();

	/**
	 * Returns the source state from which all transitions in this sequence
	 * emanate.
	 * 
	 * @return The source state from which all transitions in this sequence
	 *         emanate.
	 */
	State state();

	/**
	 * Adds transitions to this sequence.
	 * 
	 * @param transitions
	 *            The transitions to be added to this sequence.
	 */
	void addAll(Collection<Transition> transitions);

	/**
	 * Returns the number of transitions contained in this sequence.
	 * 
	 * @return The number of transitions contained in this sequence.
	 */
	int size();

	/**
	 * Returns true iff this sequence is empty.
	 * 
	 * @return Returns true iff this sequence is empty.
	 */
	boolean isEmpty();

	/**
	 * Retrieves, but not removes, the head (first element) of this transition
	 * sequence.
	 * 
	 * @return The head (first element) of this transition sequence.
	 */
	Transition peek();

	/**
	 * does this set of transitions contain all enabled transitions of the given
	 * state
	 * 
	 * @return true iff this set of transitions contain all enabled transitions
	 *         of the given state
	 */
	boolean containsAllEnabled();

	Collection<Transition> transitions();

	/**
	 * sets the flag that denotes if this transition sequence contains all
	 * enabled transitions of the state
	 */
	void setContainingAllEnabled(boolean value);
}
