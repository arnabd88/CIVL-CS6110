package edu.udel.cis.vsl.civl.predicate.IF;

/**
 * This represents a predicate in CNF, containing a number of predicates, called
 * clauses, i.e., p1 &amp; p2 &amp; ...
 * 
 * @author Manchun Zheng
 *
 */
public interface AndPredicate extends CIVLStatePredicate {
	/**
	 * Add a predicate as one clause of this And predicate.
	 */
	void addClause(CIVLStatePredicate predicate);

	/**
	 * Returns all predicates contained by this And predicate.
	 * 
	 * @return
	 */
	Iterable<CIVLStatePredicate> clauses();

	/**
	 * Returns that predicate that has a violation that not yet been reported.
	 * 
	 * @return
	 */
	CIVLStatePredicate getUnreportedViolatedPredicate();
}
