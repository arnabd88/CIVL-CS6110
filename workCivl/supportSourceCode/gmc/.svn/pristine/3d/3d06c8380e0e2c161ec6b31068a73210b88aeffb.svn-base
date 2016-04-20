package edu.udel.cis.vsl.gmc;

import java.io.PrintStream;

/**
 * An EnablerIF tells you which transitions should be explored from a given
 * state. It might need to know things about the state of the search (such as
 * what states are currently on the DFS stack). Such information can be provided
 * at creation.
 * 
 * @author Stephen F. Siegel, University of Delaware
 */
public interface EnablerIF<STATE, TRANSITION, TRANSITIONSEQUENCE> {

	/**
	 * Returns TransitionSequence of enabled transitions departing from given
	 * source state. This object encapsulates the given state and an ordered set
	 * of transitions which are enabled at that state. The TRANSITIONSEQUENCE
	 * object behaves similar to an iterator which iterates over those enabled
	 * transitions. In particular, it has state.
	 * 
	 * @returns an object encompassing the enabled transitions at the given
	 *          state, in some order, and including also the given state
	 */
	TRANSITIONSEQUENCE enabledTransitions(STATE source);

	/**
	 * Returns the source state of the sequence, i.e., the state specified when
	 * creating that sequence.
	 * 
	 * @returns the source state of the sequence
	 */
	STATE source(TRANSITIONSEQUENCE sequence);

	/**
	 * Is there a next transition in the sequence?
	 * 
	 * @param sequence
	 *            a transition sequence
	 * @return true if there is a next state, false if the transitions form the
	 *         sequence have been exhausted
	 */
	boolean hasNext(TRANSITIONSEQUENCE sequence);

	/**
	 * Moves to next transition in the sequence and returns that transition. If
	 * there is no next transition, an exception should be thrown.
	 * 
	 * @param sequence
	 *            a transition sequence
	 * @return the next transition in the sequence
	 */
	TRANSITION next(TRANSITIONSEQUENCE sequence);

	/**
	 * Returns the same value returned by method {@link #next}, but does not
	 * change the state of the sequence.
	 * 
	 * @param sequence
	 *            a transition sequence
	 * @return the current transition in that sequence
	 */
	TRANSITION peek(TRANSITIONSEQUENCE sequence);

	/**
	 * Prints the transition in some human-readable form to the given stream.
	 * 
	 * @param out
	 *            a stream to which to print
	 * @param sequence
	 *            a transition sequence
	 */
	void print(PrintStream out, TRANSITIONSEQUENCE sequence);

	/**
	 * Prints some representation of the transitions in the sequence other than
	 * the first (current) transition.
	 * 
	 * @param out
	 *            stream to which to print
	 * @param sequence
	 *            a transition sequence
	 */
	void printRemaining(PrintStream out, TRANSITIONSEQUENCE sequence);

	/**
	 * Set the debugging flag to the given value. When true, debugging output
	 * will be printed to the debugging output stream.
	 * 
	 * @param value
	 *            true if you want to print debugging info, false otherwise
	 */
	void setDebugging(boolean value);

	/**
	 * Returns the current value of the debugging flag. When true, debugging
	 * output will be be printed to the debugging output stream.
	 * 
	 * @return current value of debugging flag.
	 */
	boolean debugging();

	/**
	 * Set the debugging output stream to the given stream.
	 * 
	 * @param out
	 *            the stream to which you want the debugging output to be sent
	 */
	void setDebugOut(PrintStream out);

	/**
	 * Returns the debugging output stream. This is the stream to which debuging
	 * output will be printed when the debugging flag is on.
	 * 
	 * @return the debugging output stream
	 */
	PrintStream getDebugOut();

	/**
	 * Prints the current first transition in the sequence, preceded by the
	 * index of the transition within the sequence.
	 * 
	 * @param out
	 *            the stream to which to print
	 * @param sequence
	 *            the transition sequence
	 */
	void printFirstTransition(PrintStream out, TRANSITIONSEQUENCE sequence);

	/**
	 * Did the original sequence (before any calls to next) have more than one
	 * element?
	 * 
	 * @return true iff sequence had at least 2 elements when it was created
	 */
	boolean hasMultiple(TRANSITIONSEQUENCE sequence);

	/**
	 * Returns the number of transitions that have been removed from this
	 * sequence since it was created.
	 * 
	 * @return the number of transitions removed
	 */
	int numRemoved(TRANSITIONSEQUENCE sequence);

}
