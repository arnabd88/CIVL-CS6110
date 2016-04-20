package edu.udel.cis.vsl.gmc;

/**
 * A state predicate is basically a function which returns either true or false
 * at any state in the transition system. It is typically used to encode a "bad"
 * property, such as deadlock.
 * 
 * @author Stephen F. Siegel
 * 
 * @param <S>
 *            the type used to represent states
 */
public interface StatePredicateIF<S> {

	/**
	 * Does this predicate hold at the given state?
	 * 
	 * @param state
	 *            any state in the state-transition system
	 * @return true iff this predicate holds at the state
	 */
	boolean holdsAt(S state);

	/**
	 * Returns a human-readable explanation of why the predicate does or does
	 * not hold, after method {@link holdsAt} has been called. The information
	 * returns should correspond to the last call to {@link holdsAt}.
	 */
	String explanation();

}
