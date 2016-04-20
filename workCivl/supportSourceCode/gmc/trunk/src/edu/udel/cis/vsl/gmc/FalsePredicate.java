package edu.udel.cis.vsl.gmc;

/**
 * The state predicate which simply returns "false" at every state. This is
 * needed in some contexts. For example, a depth-first searcher requires a
 * predicate. If you want to search all reachable states, you can provide it a
 * false predicate.
 * 
 * @author Stephen F. Siegel
 * 
 * @param <S>
 *            the type used to represent states in the state-transition system
 */
public class FalsePredicate<S> implements StatePredicateIF<S> {

	/**
	 * Returns false.
	 * 
	 * @return false
	 */
	public boolean holdsAt(S state) {
		return false;
	}

	/**
	 * Returns the string "The false predicate is always false."
	 * 
	 * @return "The false predicate is always false."
	 */
	public String explanation() {
		return "The false predicate is always false.";
	}

	/**
	 * Returns the string "FalsePredicate".
	 * 
	 * @reutrn "FalsePredicate"
	 */
	public String toString() {
		return "FalsePredicate";
	}

}
